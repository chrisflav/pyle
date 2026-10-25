import Lean.Data.Json
import LeanBiscuit.Crypto.P256
import LeanBiscuit.Util.Base64
import Pyle.Crypto.Keys

/-!
# JSON Web Keys

The public half of each signing key, as the JWKS endpoint publishes it
(RFC 7517, with the curve names of RFC 7518 §6.2 and RFC 8037 §2).  Clients
pick the key to verify an ID token with by its `kid`; pyle uses the key's
RFC 7638 thumbprint as its `kid`, so the identifier is a function of the key
and cannot drift from it.

JOSE writes binary values in unpadded base64url, defined here as the smallest
thing this module and `Pyle.Oidc.Jwt` need.
-/

namespace Pyle
namespace Oidc

open Lean (Json)
open Pyle.Crypto

namespace Jose

/-- Unpadded base64url (RFC 7515 §2). -/
def b64urlEncode (b : ByteArray) : String :=
  String.ofList ((LeanBiscuit.Base64.encode b).toList.filter (· != '='))

/-- The inverse of `b64urlEncode`.  Padding is rejected, as JOSE forbids it,
and so are non-zero bits after the last whole byte. -/
def b64urlDecode? (s : String) : Option ByteArray :=
  if s.contains '=' then none else LeanBiscuit.Base64.decode? s

end Jose

namespace Jwk

/-- The members of a public JWK that identify the key, as name and value, in
the lexicographic order RFC 7638 §3 canonicalises them in. -/
def requiredMembers (algorithm : SigningAlgorithm) (publicKey : ByteArray) :
    Except String (List (String × String)) :=
  match algorithm with
  | .es256 => do
    let some point := LeanBiscuit.P256.decodePublicKey publicKey
      | throw "not a compressed P-256 point"
    let x := publicKey.extract 1 33
    let y := LeanBiscuit.Bytes.ofNatBE 32 point.Y
    pure [("crv", "P-256"), ("kty", "EC"), ("x", Jose.b64urlEncode x),
      ("y", Jose.b64urlEncode y)]
  | .edDsa =>
    if publicKey.size != 32 then throw "an Ed25519 public key is 32 bytes"
    else pure [("crv", "Ed25519"), ("kty", "OKP"), ("x", Jose.b64urlEncode publicKey)]
  | .rs256 => do
    let (n, e) ← Crypto.Ffi.rsaPublicNumbers publicKey
    pure [("e", Jose.b64urlEncode e), ("kty", "RSA"), ("n", Jose.b64urlEncode n)]

/-- The RFC 7638 thumbprint of a public key: the unpadded base64url SHA-256 of
its required members as compact JSON in lexicographic order.  Every value is
base64url or a fixed name, so none needs escaping. -/
def thumbprint (algorithm : SigningAlgorithm) (publicKey : ByteArray) : Except String String := do
  let members ← requiredMembers algorithm publicKey
  let canonical := "{" ++ ",".intercalate (members.map fun (k, v) => s!"\"{k}\":\"{v}\"") ++ "}"
  pure (Jose.b64urlEncode (LeanBiscuit.Sha256.hash canonical.toUTF8))

/-- The public JWK of a key: its required members, `use` and `alg`, and the
given `kid`. -/
def ofPublicKey (algorithm : SigningAlgorithm) (publicKey : ByteArray) (kid : String) :
    Except String Json := do
  let members ← requiredMembers algorithm publicKey
  pure <| Json.mkObj <| members.map (fun (k, v) => (k, Json.str v)) ++
    [("use", Json.str "sig"), ("alg", Json.str algorithm.joseName), ("kid", Json.str kid)]

/-- The public JWK of a signing key, with its thumbprint as `kid`. -/
def ofSigningKey (k : SigningKey) : Except String Json := do
  ofPublicKey k.algorithm k.publicKey (← thumbprint k.algorithm k.publicKey)

/-- The `kid` pyle gives a signing key: its RFC 7638 thumbprint. -/
def keyId (k : SigningKey) : Except String String :=
  thumbprint k.algorithm k.publicKey

/-- A JWK Set (RFC 7517 §5) of the public halves of the given keys, as the JWKS
endpoint serves it: the current key and the previous one (DESIGN.md §6.3). -/
def set (keys : List SigningKey) : Except String Json := do
  pure (Json.mkObj [("keys", Json.arr (← keys.mapM ofSigningKey).toArray)])

end Jwk

end Oidc
end Pyle