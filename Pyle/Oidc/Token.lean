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
  that use began, as RFC 6749 §4.1.2 asks.  The ID token and access token that
  use issued are not revoked — they are self-contained and short-lived, and
  revoking them is what the RFC's "when possible" leaves out;
* `refresh_token` — rotated by `Store.rotateRefreshToken`: the token presented
  is used up and a successor issued, and a token presented a second time
  revokes its whole family.  A narrower `scope` may be asked for the new access
  and ID tokens; the refresh token keeps the original grant.  A family expires
  `refreshTokenSeconds` after it began, however often it is rotated, and,
  unless the grant included `offline_access`, when the pyle session it came
  from ends;
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

/-- What exchanging an authorization code comes to. -/
inductive CodeDecision where
  /-- Issue tokens for the grant the code carries. -/
  | issue (code : Store.AuthCode)
  /-- The code is unknown, was used before, or has expired. -/
  | unusable
  /-- The code was issued to another client or for another redirect URI. -/
  | wrongBinding
  /-- The code verifier does not answer the code's PKCE challenge. -/
  | badVerifier

/-- Decide an authorization-code exchange (DESIGN.md §9.4), given the row the
store deleted for the code, if any, the authenticated client, and the
`redirect_uri` and `code_verifier` of the request.  Tokens are issued only for
a code that was there, has not expired at `now`, was issued to this client
for this redirect URI, and whose challenge the verifier answers.

The store already refuses an expired code; the expiry is checked again here
so that what `codeGrant` decides rests on this function alone. -/
def codeDecision (row : Option Store.AuthCode) (clientId redirectUri verifier : String)
    (now : Nat) : CodeDecision :=
  match row with
  | none => .unusable
  | some a =>
    if ¬ now < a.expires then .unusable
    else if a.clientId ≠ clientId ∨ a.redirectUri ≠ redirectUri then .wrongBinding
    else if Pkce.verifies verifier a.codeChallenge = false then .badVerifier
    else .issue a

/-- The client's minimum level, if a sign-in with this `amr` falls below it,
or reads as no level at all.  `/authorize` checked it when the code was
issued, but the minimum may have been raised since — between the code and its
exchange, or during the life of a refresh-token family — and the token
endpoint answers to the minimum as it is now. -/
def belowMinimum (ctx : Ctx) (client : Store.Client) (amr : List String) : IO (Option Acr) := do
  let need := ((← ctx.store.clientSettings client.id).getD {}).minAcr
  return if (Acr.ofAmr amr).any (·.satisfies need) then none else some need

/-- The `invalid_grant` for a sign-in below the client's minimum. -/
def tooWeakGrant (need : Acr) : Reply :=
  oauthError "invalid_grant" s!"the sign-in is below this client's minimum, {need.identifier}"

/-- The authorization-code grant.  The code is deleted first, whatever comes
next, and `codeDecision` decides on what was deleted. -/
def codeGrant (ctx : Ctx) (r : Req) (client : Store.Client) (form : List (String × String)) :
    IO Reply := do
  let some code := lookupOnce form "code" | return oauthError "invalid_request" "code is required"
  let some redirectUri := lookupOnce form "redirect_uri"
    | return oauthError "invalid_request" "redirect_uri is required"
  let some verifier := lookupOnce form "code_verifier"
    | return oauthError "invalid_request" "code_verifier is required"
  let now ← ctx.clock
  let h := tokenHash code
  let session ← ctx.store.codeSession h
  let row ← ctx.store.consumeCode h now
  match codeDecision row client.id redirectUri verifier now with
  | .unusable =>
    let family := familyOfCode h
    if ← ctx.store.familyExists family then
      discard <| ctx.store.revokeRefreshFamily family now
      Audit.log ctx r .refreshReuse .refused (detail := s!"code reused by {client.id}")
    return oauthError "invalid_grant" "the code is unknown, used or expired"
  | .wrongBinding =>
    return oauthError "invalid_grant" "the code was issued for another client or redirect URI"
  | .badVerifier =>
    return oauthError "invalid_grant" "the code verifier does not match the challenge"
  | .issue a =>
    let some user ← liveUser ctx a.user | return oauthError "invalid_grant" "the account is gone"
    if let some need ← belowMinimum ctx client a.amr then return tooWeakGrant need
    let refresh ← startRefresh ctx (familyOfCode h) client user a.scope a.amr a.authTime session
      a.acr
    tokenResponse ctx r client user a.scope a.amr a.authTime a.nonce (some refresh)
      "authorization_code" a.acr

/-- The refresh-token grant. -/
def refreshGrant (ctx : Ctx) (r : Req) (client : Store.Client)
    (form : List (String × String)) : IO Reply := do
  let some old := lookupOnce form "refresh_token"
    | return oauthError "invalid_request" "refresh_token is required"
  let now ← ctx.clock
  let new ← randomToken
  -- Rotation never extends the family past its absolute expiry.
  let cap := (← ctx.store.familyExpiry (tokenHash old)).getD (now + ctx.config.refreshTokenSeconds)
  match ← ctx.store.rotateRefreshToken (tokenHash old) (tokenHash new) client.id now
      (min cap (now + ctx.config.refreshTokenSeconds)) with
  | .invalid => return oauthError "invalid_grant" "the refresh token is unknown or expired"
  | .reused =>
    Audit.log ctx r .refreshReuse .refused (detail := s!"refresh token reused by {client.id}")
    return oauthError "invalid_grant" "the refresh token was already used"
  | .rotated g =>
    let some user ← liveUser ctx g.user | return oauthError "invalid_grant" "the account is gone"
    if let some need ← belowMinimum ctx client g.amr then
      -- The family cannot meet the client's minimum again: end it.
      discard <| ctx.store.revokeRefreshFamily g.family now
      Audit.log ctx r .tokenIssued .refused (userName := some user.name)
        (detail := s!"refresh for {client.id} below {need.identifier}; family revoked")
      return tooWeakGrant need
    let granted := words g.scope
    let scope ← match lookupOnce form "scope" with
      | none => pure g.scope
      | some s =>
        let asked := words s
        unless asked.all granted.contains do
          return oauthError "invalid_scope" "the scope exceeds the original grant"
        pure (" ".intercalate asked)
    tokenResponse ctx r client user scope g.amr g.authTime none (some new) "refresh_token" g.acr

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