import Pyle.Device.Grant
import Pyle.Oidc.Pkce

/-!
# The token endpoint

`POST /token` (RFC 6749 §3.2) answers three grants, each after the client has
authenticated (`Oidc.authenticateClient`):

* `authorization_code` — the code is consumed whatever happens next, and
  tokens are issued only if it was issued to this client, for this
  `redirect_uri`, with a challenge `code_verifier` answers (DESIGN.md §9.4).  A
  code presented again after its first use revokes the refresh-token family
  that use began, as RFC 6749 §4.1.2 asks;
* `refresh_token` — rotated by `Store.rotateRefreshToken`: the token presented
  is used up and a successor issued, and a token presented a second time
  revokes its whole family.  A narrower `scope` may be asked for the new access
  and ID tokens; the refresh token keeps the original grant;
* `urn:ietf:params:oauth:grant-type:device_code` — the device grant's poll
  (`Device.poll`).

The route is exempt from the `Origin` check: relying parties call it from
their servers, and it never sees a cookie.  Every reply carries
`Cache-Control: no-store` (RFC 6749 §5.1).
-/

namespace Pyle
namespace Oidc

open Http

/-- The account a grant names, if it still exists and is not disabled. -/
def liveUser (ctx : Ctx) (id : Store.UserId) : IO (Option Store.User) := do
  return (← ctx.store.findUser id).filter (!·.disabled)

/-- The authorization-code grant. -/
def codeGrant (ctx : Ctx) (r : Req) (client : Store.Client) (form : List (String × String)) :
    IO Reply := do
  let some code := lookupOnce form "code" | return oauthError "invalid_request" "code is required"
  let some redirectUri := lookupOnce form "redirect_uri"
    | return oauthError "invalid_request" "redirect_uri is required"
  let some verifier := lookupOnce form "code_verifier"
    | return oauthError "invalid_request" "code_verifier is required"
  let now ← ctx.clock
  let h := tokenHash code
  let some a ← ctx.store.consumeCode h now
    | let family := familyOfCode h
      if ← ctx.store.familyExists family then
        discard <| ctx.store.revokeRefreshFamily family now
        Audit.log ctx r .refreshReuse .refused (detail := s!"code reused by {client.id}")
      return oauthError "invalid_grant" "the code is unknown, used or expired"
  if a.clientId != client.id || a.redirectUri != redirectUri then
    return oauthError "invalid_grant" "the code was issued for another client or redirect URI"
  unless Pkce.verifies verifier a.codeChallenge do
    return oauthError "invalid_grant" "the code verifier does not match the challenge"
  let some user ← liveUser ctx a.user | return oauthError "invalid_grant" "the account is gone"
  let refresh ← startRefresh ctx (familyOfCode h) client user a.scope a.amr a.authTime
  tokenResponse ctx r client user a.scope a.amr a.authTime a.nonce (some refresh)
    "authorization_code"

/-- The refresh-token grant. -/
def refreshGrant (ctx : Ctx) (r : Req) (client : Store.Client)
    (form : List (String × String)) : IO Reply := do
  let some old := lookupOnce form "refresh_token"
    | return oauthError "invalid_request" "refresh_token is required"
  let now ← ctx.clock
  let new ← randomToken
  match ← ctx.store.rotateRefreshToken (tokenHash old) (tokenHash new) client.id now
      (now + ctx.config.refreshTokenSeconds) with
  | .invalid => return oauthError "invalid_grant" "the refresh token is unknown or expired"
  | .reused =>
    Audit.log ctx r .refreshReuse .refused (detail := s!"refresh token reused by {client.id}")
    return oauthError "invalid_grant" "the refresh token was already used"
  | .rotated g =>
    let some user ← liveUser ctx g.user | return oauthError "invalid_grant" "the account is gone"
    let granted := words g.scope
    let scope ← match lookupOnce form "scope" with
      | none => pure g.scope
      | some s =>
        let asked := words s
        unless asked.all granted.contains do
          return oauthError "invalid_scope" "the scope exceeds the original grant"
        pure (" ".intercalate asked)
    tokenResponse ctx r client user scope g.amr g.authTime none (some new) "refresh_token"

/-- `POST /token`. -/
def token : Handler := fun ctx r => do
  let .ok form := r.form | return oauthError "invalid_request" "the body must be a form"
  let client ← match ← authenticateClient ctx.store r form with
    | .ok (c, _) => pure c
    | .error e => return e.reply
  match lookupOnce form "grant_type" with
  | some "authorization_code" => codeGrant ctx r client form
  | some "refresh_token" => refreshGrant ctx r client form
  | some g =>
    if g == Device.grantType then Device.poll ctx r client form
    else return oauthError "unsupported_grant_type" "that grant type is not supported"
  | none => return oauthError "invalid_request" "grant_type is required"

end Oidc
end Pyle