import Pyle.Oidc.Authorize
import Pyle.Oidc.Token
import Pyle.Oidc.UserInfo
import Pyle.Oidc.Logout
import Pyle.Oidc.Discovery
import Pyle.Token.Attest
import Pyle.ForwardAuth

/-!
# The protocol routes

Every endpoint of DESIGN.md §5, as one list for `Pyle.Server.routes`.  The
routes called by servers and command-line clients, which authenticate their
callers themselves and must never act on a browser's session, are exempt from
the `Origin` check (and so never see a cookie): the token endpoint, device
authorization, `POST /userinfo`, the bearer form of the kleis attestation, and
`POST /authorize` and `POST /end_session`, which only turn themselves into
`GET`s.
-/

namespace Pyle
namespace Oidc

open Http

/-- Every protocol route. -/
def routes : List Route := [
  .mk' .get "/.well-known/openid-configuration" discovery,
  .mk' .get "/jwks" jwks,
  .mk' .get "/biscuit/keys" biscuitKeys,
  .mk' .get "/authorize" authorize,
  .mk' .post "/authorize" authorizePost (csrf := .exempt),
  .mk' .post "/token" token (csrf := .exempt),
  .mk' .get "/userinfo" userinfo,
  .mk' .post "/userinfo" userinfo (csrf := .exempt),
  .mk' .get "/end_session" endSession,
  .mk' .post "/end_session" endSessionPost (csrf := .exempt),
  .mk' .post "/end_session/confirm" confirmLogout,
  .mk' .post "/device_authorization" Device.authorization (csrf := .exempt),
  .mk' .get "/device" Device.pageGet,
  .mk' .post "/device" Device.pagePost,
  .mk' .post "/kleis/attest" Token.attestBearer (csrf := .exempt),
  .mk' .post "/kleis/attest/session" Token.attestSession,
  .mk' .get "/forward-auth" ForwardAuth.check,
  .mk' .get "/forward-auth/grant" ForwardAuth.grant
]

end Oidc
end Pyle