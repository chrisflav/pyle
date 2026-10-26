import Pyle.Oidc.Common
import Pyle.Keys.Lifecycle
import Pyle.Device.Grant

/-!
# Discovery and published keys

`GET /.well-known/openid-configuration` (OpenID Connect Discovery 1.0 §3,
with RFC 8414's additions) says what pyle supports, and only that: the code
flow with `S256`, the three client authentication methods, and the response
`iss` of RFC 9207.  Request objects are not supported, which has to be said
out loud, since `request_uri_parameter_supported` defaults to true.

`GET /jwks` publishes the ID-token keys of both algorithms (RFC 7517): for
each, the next key — so that clients have it before it signs — the current one
and the previous one, so that tokens it signed still verify.

`GET /biscuit/keys` publishes the biscuit root keys in the same three states,
for services verifying access tokens (`Pyle.Token.Verify`) and for kleis
grants trusting pyle's attestations.  They are kept out of the JWKS so that an
OpenID Connect client never meets a key it was not written for.
-/

namespace Pyle
namespace Oidc

open Http
open Lean (Json)

/-- The scopes pyle knows. -/
def scopesSupported : List String :=
  ["openid", "profile", "groups", "offline_access", "kleis"]

/-- The claims ID tokens and `/userinfo` carry. -/
def claimsSupported : List String :=
  ["iss", "sub", "aud", "exp", "iat", "auth_time", "nonce", "amr", "acr", accountAcrClaim, "name",
   "groups"]

/-- The discovery document. -/
def discoveryDocument (issuer : String) : Json :=
  let strs (xs : List String) : Json := Json.arr (xs.map Json.str).toArray
  Json.mkObj [
    ("issuer", Json.str issuer),
    ("authorization_endpoint", Json.str (issuer ++ "/authorize")),
    ("token_endpoint", Json.str (issuer ++ "/token")),
    ("userinfo_endpoint", Json.str (issuer ++ "/userinfo")),
    ("jwks_uri", Json.str (issuer ++ "/jwks")),
    ("end_session_endpoint", Json.str (issuer ++ "/end_session")),
    ("device_authorization_endpoint", Json.str (issuer ++ "/device_authorization")),
    ("biscuit_keys_uri", Json.str (issuer ++ "/biscuit/keys")),
    ("scopes_supported", strs scopesSupported),
    ("response_types_supported", strs ["code"]),
    ("response_modes_supported", strs ["query"]),
    ("grant_types_supported", strs ["authorization_code", "refresh_token", Device.grantType]),
    ("subject_types_supported", strs ["public"]),
    ("id_token_signing_alg_values_supported", strs ["ES256", "RS256"]),
    ("token_endpoint_auth_methods_supported",
      strs ["client_secret_basic", "client_secret_post", "none"]),
    ("code_challenge_methods_supported", strs ["S256"]),
    ("claims_supported", strs claimsSupported),
    ("acr_values_supported", strs (Acr.all.map (·.identifier))),
    ("prompt_values_supported", strs ["none", "login"]),
    ("authorization_response_iss_parameter_supported", Json.bool true),
    ("claims_parameter_supported", Json.bool true),
    ("request_parameter_supported", Json.bool false),
    ("request_uri_parameter_supported", Json.bool false)]

/-- `GET /.well-known/openid-configuration`. -/
def discovery : Handler := fun ctx _ => do
  return (Reply.json (discoveryDocument ctx.config.issuer)).withHeader "Cache-Control"
    "public, max-age=3600"

/-- `GET /jwks`. -/
def jwks : Handler := fun ctx _ => do
  let now ← ctx.clock
  let mut keys := #[]
  for use in [Keys.Use.idTokenEs256, .idTokenRs256] do
    Keys.ensure ctx.store ctx.rootKey use now
    for k in ← Keys.published ctx.store use do
      let some alg := Crypto.SigningAlgorithm.ofJoseName? k.algorithm | continue
      match Jwk.ofPublicKey alg k.publicKey k.kid with
      | .ok j => keys := keys.push j
      | .error _ => pure ()
  return (Reply.json (Json.mkObj [("keys", Json.arr keys)])).withHeader "Cache-Control"
    "public, max-age=300"

/-- `GET /biscuit/keys`: each published root key as `ed25519/<hex>`, the form a
kleis grant names it in, with its state. -/
def biscuitKeys : Handler := fun ctx _ => do
  let now ← ctx.clock
  Keys.ensure ctx.store ctx.rootKey .biscuitRoot now
  let keys ← Keys.published ctx.store .biscuitRoot
  let entries := keys.map fun k => Json.mkObj
    [("kid", Json.str k.kid), ("state", Json.str k.state.toString),
     ("public_key", Json.str (LeanBiscuit.PublicKey.print ⟨.ed25519, k.publicKey⟩))]
  return (Reply.json (Json.mkObj [("keys", Json.arr entries)])).withHeader "Cache-Control"
    "public, max-age=300"

end Oidc
end Pyle