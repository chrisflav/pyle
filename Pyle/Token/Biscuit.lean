import Pyle.Keys.Lifecycle
import Pyle.Token.Verify

/-!
# Issuing biscuits

pyle's access tokens are biscuits whose authority block says who the user is,
how and when they signed in, which groups they are in and which client the
token was issued to and with which scopes, and which carries an expiry check and an audience check
(DESIGN.md §5.2; `Pyle.Token.Verify` shows the block).  The same root key signs
the third-party blocks pyle attests for kleis (§5.4).

**Signing.**  The root key is long-lived, so it never meets `lean-biscuit`'s
curve arithmetic (§6.2): the authority block and attestations are signed
through `Biscuit.createWith` and `signThirdPartyBlockWith` with a signer that
calls OpenSSL (`SigningKey.sign`).  The ephemeral next key, whose secret travels
in the token so that its holder can attenuate it, is 32 random bytes handled in
Lean; it signs at most one block.

**Datalog source.**  The blocks are written as datalog text and parsed by
`lean-biscuit`.  Every string spliced into them goes through `quote`, which
escapes exactly what the parser treats specially, and dates are formatted here;
nothing a request supplies reaches the source unquoted.
-/

namespace Pyle
namespace Token

open LeanBiscuit LeanBiscuit.Token

/-- A string as a datalog string literal: `\` and `"` escaped, a line break
written `\n`, as `lean-biscuit`'s parser reads them back. -/
def quote (s : String) : String :=
  "\"" ++ s.foldl (init := "") (fun out c =>
    match c with
    | '\\' => out ++ "\\\\"
    | '"' => out ++ "\\\""
    | '\n' => out ++ "\\n"
    | c => out.push c) ++ "\""

/-- A time as a datalog date literal (RFC 3339, UTC). -/
def date (t : Nat) : String := (Time.formatRfc3339 t).getD "1970-01-01T00:00:00Z"

/-- What an access token says. -/
structure Grant where
  /-- The user's name. -/
  user : String
  /-- The authentication methods of the sign-in. -/
  amr : List String
  /-- The level of the sign-in, as its identifier. -/
  acr : String := ""
  /-- The account's strongest level, as its identifier, if it has one. -/
  accountAcr : Option String := none
  /-- When the user authenticated. -/
  authTime : Nat
  /-- The user's groups. -/
  groups : List String
  /-- The client the token was issued to. -/
  client : String
  /-- The services that may accept it. -/
  audience : List String
  /-- The OAuth scopes granted. -/
  scopes : List String := []

/-- The audience pyle itself accepts an access token under, at `/userinfo` and
`/kleis/attest`. -/
def pyleAudience : String := "pyle"

/-- The authority block of an access token expiring at `expires`. -/
def authoritySource (g : Grant) (expires : Nat) : String :=
  let facts := [s!"user({quote g.user});"] ++ g.amr.map (s!"amr({quote ·});") ++
    (if g.acr.isEmpty then [] else [s!"acr({quote g.acr});"]) ++
    (g.accountAcr.map fun a => [s!"account_acr({quote a});"]).getD [] ++
    [s!"auth_time({date g.authTime});"] ++ g.groups.map (s!"group({quote ·});") ++
    [s!"client({quote g.client});"] ++ g.scopes.map (s!"scope({quote ·});")
  let checks := [s!"check if time($t), $t < {date expires};",
    s!"check if audience($a), \{{", ".intercalate (g.audience.map quote)}}.contains($a);"]
  "\n".intercalate (facts ++ checks)

/-- The biscuit root key in `lean-biscuit`'s form. -/
def rootPublicKey (k : Crypto.SigningKey) : PublicKey := ⟨.ed25519, k.publicKey⟩

/-- The published biscuit root keys — next, current and previous — in
`lean-biscuit`'s form, for verifying. -/
def publishedRoots (store : Store.Store) : IO (List PublicKey) := do
  return (← Keys.published store .biscuitRoot).toList.map fun k => ⟨.ed25519, k.publicKey⟩

/-- A fresh ephemeral key for the next block. -/
def ephemeralKey : IO PrivateKey := return ⟨.ed25519, ← Crypto.randomBytes 32⟩

/-- Sign through OpenSSL with a signing key, as a `lean-biscuit` signer. -/
def signer (k : Crypto.SigningKey) (payload : ByteArray) : IO ByteArray := k.sign payload

/-- Issue an access token for a grant, valid until `expires`, signed by the
current biscuit root key.  Its base64url text. -/
def issue (store : Store.Store) (rootKey : ByteArray) (g : Grant) (now expires : Nat) :
    IO String := do
  let (_, root) ← Keys.current store rootKey .biscuitRoot now
  let authority ← match BlockBuilder.code {} (authoritySource g expires) with
    | .ok b => pure b
    | .error e => throw (.userError s!"token: the authority block does not parse: {repr e}")
  let next ← ephemeralKey
  match ← (Biscuit.createWith (rootPublicKey root) (signer root) next authority).run with
  | .ok b => return b.toBase64
  | .error e => throw (.userError s!"token: cannot create a biscuit: {repr e}")

/-- Verify an access token for pyle itself at `now` under the published root
keys. -/
def verifyForPyle (store : Store.Store) (token : String) (now : Nat) :
    IO (Except String Identity) := do
  return verify (← publishedRoots store) pyleAudience now token

/-- The contents of a third-party block attesting a user to kleis (§5.4):
`user`, `amr`, `acr` and `group` facts and a check that the block is used
before `expires`.  Signed by the current biscuit root key through OpenSSL in answer to
a token's third-party block request. -/
def attest (store : Store.Store) (rootKey : ByteArray) (request : Proto.ThirdPartyBlockRequest)
    (user : String) (amr groups : List String) (now expires : Nat) (acr : String := "") :
    IO (Proto.ThirdPartyBlockContents × PublicKey) := do
  let (_, root) ← Keys.current store rootKey .biscuitRoot now
  let source := "\n".intercalate ([s!"user({quote user});"] ++ amr.map (s!"amr({quote ·});") ++
    (if acr.isEmpty then [] else [s!"acr({quote acr});"]) ++
    groups.map (s!"group({quote ·});") ++ [s!"check if time($t), $t < {date expires};"])
  let block ← match BlockBuilder.code {} source with
    | .ok b => pure b
    | .error e => throw (.userError s!"token: the attestation does not parse: {repr e}")
  let signed := Biscuit.signThirdPartyBlockWith (rootPublicKey root) (signer root) request block
  match ← signed.run with
  | .ok contents => return (contents, rootPublicKey root)
  | .error e => throw (.userError s!"token: cannot sign an attestation: {repr e}")

end Token
end Pyle