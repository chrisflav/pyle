import Pyle.Oidc.Common
import Pyle.Oidc.Jwt
import Pyle.Keys.Lifecycle
import Pyle.Store.Protocols

/-!
# ID tokens

What an OpenID Connect client learns about the user (OpenID Connect Core
§2): a JWT with

* `iss` — this issuer; `aud` — the client; `sub` — the account's random user
  handle in base64url, never its name, so the identifier says nothing and
  survives a rename;
* `iat`, `exp` — issued now, good for `idTokenSeconds`;
* `auth_time` — when the user authenticated, which may be long before;
* `nonce` — the one the authorization request carried, if any;
* `amr` (RFC 8176) and `acr` — how: `acr` is the level of the sign-in
  (`Acr`, read back from the `amr`), or, when the authorization request asked
  for `acr` as an essential claim, the first of its values the level meets
  (`AcrRequest.claim`);
* `pyle_account_acr` — the strongest level the account could sign in at,
  given what it has registered (`Acr.Capabilities.level`), so that a service
  can tell an account that has no passkey from one that chose not to use it;
  absent for an account that could not sign in again;
* `name` and `preferred_username` when the scope includes `profile` — the
  display name (the account name if it has none) and the account name;
  `email` and `email_verified` when it includes `email` and the account has
  an address; `groups` when it includes `groups` (`scopedClaims`).

It is signed with the client's algorithm: ES256 unless the client was
registered for RS256, with the current key of that algorithm, named in the
header by its `kid` so that a client finds it in the JWKS.
-/

namespace Pyle
namespace Oidc

open Lean (Json)

/-- The claim naming the account's strongest level. -/
def accountAcrClaim : String := "pyle_account_acr"

/-- The `pyle_account_acr` claim for an account's strongest level, if it has
one.  Shared by ID tokens and `/userinfo`. -/
def accountClaims (account : Option Acr) : List (String × Json) :=
  (account.map fun a => [(accountAcrClaim, Json.str a.identifier)]).getD []

/-- The claims about the user that a scope releases.  Shared by ID tokens and
`/userinfo`:

* `profile`: `name`, the display name if the account has one and its name
  otherwise, and `preferred_username`, always its name;
* `email`: `email` and `email_verified`, `true`, if the account has an
  address — an administrator set it, never the user — and neither if not;
* `groups`: `groups`. -/
def scopedClaims (u : Store.User) (scopes : List String) : List (String × Json) :=
  (if scopes.contains "profile" then
    [("name", Json.str (u.displayName.getD u.name)), ("preferred_username", Json.str u.name)]
   else []) ++
  (match u.email with
   | some e => if scopes.contains "email" then
       [("email", Json.str e), ("email_verified", Json.bool true)] else []
   | none => []) ++
  (if scopes.contains "groups" then [("groups", Json.arr (u.groups.map Json.str).toArray)]
   else [])

/-- The claims of an ID token for a grant of `scopes`. -/
def idTokenClaims (issuer clientId : String) (u : Store.User) (scopes amr : List String)
    (acr : String) (account : Option Acr) (authTime : Option Nat) (nonce : Option String)
    (now expires : Nat) : Json :=
  Json.mkObj <|
    [("iss", Json.str issuer), ("sub", Json.str (subjectOf u)), ("aud", Json.str clientId),
     ("exp", (expires : Json)), ("iat", (now : Json))] ++
    (authTime.map fun t => [("auth_time", (t : Json))]).getD [] ++
    (nonce.map fun n => [("nonce", Json.str n)]).getD [] ++
    [("amr", Json.arr (amr.map Json.str).toArray), ("acr", Json.str acr)] ++
    accountClaims account ++ scopedClaims u scopes

/-- The key use a client's ID tokens are signed with. -/
def idTokenUse (settings : Store.ClientSettings) : Keys.Use :=
  if settings.idTokenAlg == "RS256" then .idTokenRs256 else .idTokenEs256

/-- Sign an ID token for a client with its algorithm's current key. -/
def signIdToken (store : Store.Store) (rootKey : ByteArray) (settings : Store.ClientSettings)
    (claims : Json) (now : Nat) : IO String := do
  let (kid, k) ← Keys.current store rootKey (idTokenUse settings) now
  Jwt.sign k kid claims

end Oidc
end Pyle