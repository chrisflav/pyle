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
* `amr` (RFC 8176) and `acr` (`phr` or `mfa`, `Oidc.acrOf`) — how;
* `name` and `groups` — the account's name and groups.

It is signed with the client's algorithm: ES256 unless the client was
registered for RS256, with the current key of that algorithm, named in the
header by its `kid` so that a client finds it in the JWKS.
-/

namespace Pyle
namespace Oidc

open Lean (Json)

/-- The claims of an ID token. -/
def idTokenClaims (issuer clientId : String) (u : Store.User) (amr : List String)
    (authTime : Option Nat) (nonce : Option String) (now expires : Nat) : Json :=
  Json.mkObj <|
    [("iss", Json.str issuer), ("sub", Json.str (subjectOf u)), ("aud", Json.str clientId),
     ("exp", (expires : Json)), ("iat", (now : Json))] ++
    (authTime.map fun t => [("auth_time", (t : Json))]).getD [] ++
    (nonce.map fun n => [("nonce", Json.str n)]).getD [] ++
    [("amr", Json.arr (amr.map Json.str).toArray), ("acr", Json.str (acrOf amr)),
     ("name", Json.str u.name), ("groups", Json.arr (u.groups.map Json.str).toArray)]

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