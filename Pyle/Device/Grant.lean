import Pyle.Oidc.Issue
import Pyle.Oidc.Client

/-!
# The device authorization grant

Command-line clients and agents sign their user in with RFC 8628 (DESIGN.md
§5.5): the client asks `/device_authorization` for a device code and a user
code, shows the user code and `/device`, and polls `/token` with the device
code while the user approves it in a browser.

* **User codes** are eight characters from RFC 8628 §6.1's base-20 alphabet
  `BCDFGHJKLMNPQRSTVWXZ` — no vowels, so no words, and nothing that looks like
  a digit — shown as `XXXX-XXXX`.  What the user types is read case-blind and
  with any separators dropped.  20⁸ codes and the limiter on the approval page
  keep guessing a live one out of reach.
* **Approving** needs a session at `phr` or better, or at the client's
  minimum (`--min-acr`) if that is higher: a CLI's token is as good
  as the passkey that approved it, and an approval page is exactly what a
  phishing site would imitate.  Without one the browser is sent to sign in with
  `acr=phr`.  The page shows which client asks and for what before the user
  decides, and the decision is a form `POST`, under the `Origin` check.  The
  tokens issued record the approving session's `amr`, and so its level, and
  the poll checks that level against the client's minimum once more.
* **Polling** answers `authorization_pending` until a decision, `slow_down` to
  a client polling faster than the interval, `access_denied` once denied,
  `expired_token` once expired; an approved code yields tokens once, with a
  refresh token whose family is begun there.  `slow_down` also adds five
  seconds to the code's interval (§3.5), and only the client a code was issued
  to can poll it: another client's poll changes nothing.  The family is not
  tied to the browser session that approved it — the device is another device,
  and signing out of the browser should not sign it out — but it expires like
  every family.
-/

namespace Pyle
namespace Device

open Http
open Oidc
open Lean (Json)

/-- The grant type a device-code token request names. -/
def grantType : String := "urn:ietf:params:oauth:grant-type:device_code"

/-- RFC 8628 §6.1's base-20 alphabet for user codes. -/
def alphabet : List Char := "BCDFGHJKLMNPQRSTVWXZ".toList

/-- The length of a user code, without its separator. -/
def userCodeLength : Nat := 8

/-- A fresh user code, as stored: eight characters of `alphabet`.  Each comes
from a random byte below 240, so that every character is equally likely. -/
partial def newUserCode : IO String := do
  let mut out := ""
  while out.length < userCodeLength do
    let b ← Crypto.randomBytes 16
    for x in b.toList do
      if x.toNat < 240 && out.length < userCodeLength then
        out := out.push (alphabet.getD (x.toNat % 20) 'B')
  return out

/-- A stored user code as it is shown: `XXXX-XXXX`. -/
def display (code : String) : String :=
  (code.take 4).toString ++ "-" ++ (code.drop 4).toString

/-- What a user typed, as a stored user code: upper-cased, with everything
outside the alphabet dropped — separators, spaces.  `none` unless exactly
eight characters remain. -/
def normalise (typed : String) : Option String :=
  let cs := typed.toUpper.toList.filter alphabet.contains
  if cs.length == userCodeLength && typed.length ≤ 32 then some (String.ofList cs) else none

/-- `POST /device_authorization` (RFC 8628 §3.1): authenticate the client as
the token endpoint does, record a device code and a user code, and answer
with both and where to go. -/
def authorization : Handler := fun ctx r => do
  let .ok form := r.form | return oauthError "invalid_request" "the body must be a form"
  let client ← match ← authenticateClient ctx.store r form with
    | .ok (c, _) => pure c
    | .error e => return e.reply
  let scopes := words ((lookupOnce form "scope").getD "openid")
  unless scopes.all client.scopes.contains do
    return oauthError "invalid_scope" "the client may not ask for that scope"
  let now ← ctx.clock
  let deviceCode ← randomToken
  let expires := now + ctx.config.deviceCodeSeconds
  -- A user code is unique while it is stored; on the rare collision, draw again.
  let mut userCode := ""
  for _ in [0:5] do
    if userCode.isEmpty then
      let candidate ← newUserCode
      try
        ctx.store.addDeviceCode (tokenHash deviceCode)
          { userCode := candidate, clientId := client.id, scope := " ".intercalate scopes,
            interval := ctx.config.devicePollSeconds, expires }
        userCode := candidate
      catch _ => pure ()
  if userCode.isEmpty then return oauthError "server_error" "" .internalServerError
  let uri := issuerUrl ctx "/device"
  return noStore <| Reply.json <| Json.mkObj
    [("device_code", Json.str deviceCode), ("user_code", Json.str (display userCode)),
     ("verification_uri", Json.str uri),
     ("verification_uri_complete",
       Json.str (uri ++ "?" ++ queryString [("user_code", display userCode)])),
     ("expires_in", (ctx.config.deviceCodeSeconds : Json)),
     ("interval", (ctx.config.devicePollSeconds : Json))]

/-- The level approving a device code for a client needs: `phr`, or the
client's own minimum if that is higher. -/
def approvalLevel (ctx : Ctx) (clientId : String) : IO Acr :=
  return Acr.max .phr ((← ctx.store.clientSettings clientId).getD {}).minAcr

/-- Answer a device-code token request (RFC 8628 §3.4, §3.5) from an
authenticated client.  The approving session's level is checked again against
what the client needs now, in case its minimum was raised in between. -/
def poll (ctx : Ctx) (r : Req) (client : Store.Client) (form : List (String × String)) :
    IO Reply := do
  let some deviceCode := lookupOnce form "device_code"
    | return oauthError "invalid_request" "device_code is required"
  let now ← ctx.clock
  let some outcome ← ctx.store.pollDeviceCodeFor (tokenHash deviceCode) client.id now
    | return oauthError "invalid_grant" "the device code was issued to another client"
  match outcome with
  | .pending => return oauthError "authorization_pending" "the user has not decided yet"
  | .slowDown => return oauthError "slow_down" "poll less often"
  | .denied => return oauthError "access_denied" "the user refused"
  | .expired => return oauthError "expired_token" "the device code has expired"
  | .approved clientId scope userId amr authTime =>
    if clientId != client.id then
      return oauthError "invalid_grant" "the device code was issued to another client"
    let some user ← ctx.store.findUser userId
      | return oauthError "invalid_grant" "the account is gone"
    if user.disabled then return oauthError "invalid_grant" "the account is disabled"
    let need ← approvalLevel ctx client.id
    unless (Acr.ofAmr amr).satisfies need do
      return oauthError "invalid_grant" s!"the approval was not at {need.identifier} or better"
    let family ← Crypto.randomBytes 32
    let refresh ← startRefresh ctx family client user scope amr authTime none
    tokenResponse ctx r client user scope amr authTime none (some refresh) "device_code"

/-- The form a user types a code into. -/
def codeForm (prefill : String) : String :=
  "<form method=\"get\" action=\"/device\">\n" ++
  "<label for=\"user_code\">Code shown by the device</label>\n" ++
  s!"<input id=\"user_code\" name=\"user_code\" value=\"{htmlEscape prefill}\" " ++
  "autocomplete=\"off\" autocapitalize=\"characters\" spellcheck=\"false\" required>\n" ++
  "<button type=\"submit\">Continue</button>\n</form>"

/-- Send the browser to sign in with a phishing-resistant authenticator, and
back to the device page with what it was given. -/
def needSignin (r : Req) : Reply :=
  signinRedirect (Req.pathAndQuery r) (acr := some .phr)

/-- The session of a request, if it is phishing-resistant: at `phr` or
better. -/
def strongSession (ctx : Ctx) (r : Req) : IO (Option Session) := do
  return (← Session.current ctx r).filter (·.level.satisfies .phr)

/-- Look a typed user code up, through the rate limiter for the signed-in
user and the client's address: a wrong code counts as a failure. -/
def lookup (ctx : Ctx) (r : Req) (s : Session) (typed : String) :
    IO (Except String (String × Store.DeviceCode)) := do
  let now ← ctx.clock
  let name := (← ctx.store.findUser s.user).map (·.name)
  match ← ctx.limiter.tryAcquire name r.clientAddress now with
  | .error wait => return .error s!"Too many wrong codes; try again in {wait} seconds."
  | .ok attempt =>
    let some code := normalise typed | return .error "That is not a code pyle gave out."
    match ← ctx.store.findPendingDeviceCode code now with
    | some d =>
      ctx.limiter.succeed attempt
      return .ok (code, d)
    | none => return .error "That code is unknown or has expired."

/-- `GET /device`: the form for the user code, or, given one, what it asks for
and the buttons to approve or deny it. -/
def pageGet : Handler := fun ctx r => do
  let some s ← strongSession ctx r | return needSignin r
  let ps := (r.queryParams.toOption).getD []
  let some typed := lookupOnce ps "user_code"
    | return page "Connect a device" ("<p>Enter the code your device shows.</p>\n" ++ codeForm "")
  match ← lookup ctx r s typed with
  | .error msg =>
    return page "Connect a device" (s!"<p class=\"error\">{htmlEscape msg}</p>\n" ++ codeForm typed)
      .badRequest
  | .ok (code, d) =>
    let need ← approvalLevel ctx d.clientId
    unless s.level.satisfies need do
      return signinRedirect (Req.pathAndQuery r) (acr := some need)
    let clientName := ((← ctx.store.findClient d.clientId).map (·.name)).getD d.clientId
    return page "Connect a device" <|
      s!"<p><strong>{htmlEscape clientName}</strong> asks to act for you with the scope " ++
      s!"<code>{htmlEscape d.scope}</code>.  Approve only if you started this on a device " ++
      s!"that shows the code <strong>{htmlEscape (display code)}</strong>.</p>\n" ++
      "<form method=\"post\" action=\"/device\">\n" ++
      s!"<input type=\"hidden\" name=\"user_code\" value=\"{htmlEscape code}\">\n" ++
      "<button type=\"submit\" name=\"decision\" value=\"approve\">Approve</button>\n" ++
      "<button type=\"submit\" name=\"decision\" value=\"deny\">Deny</button>\n</form>"

/-- `POST /device`: record the user's decision on a user code. -/
def pagePost : Handler := fun ctx r => do
  let some s ← strongSession ctx r | return signinRedirect "/device" (acr := some .phr)
  let malformed := page "Connect a device" "<p>The form is malformed.</p>" .badRequest
  let .ok form := r.form | return malformed
  let some typed := lookupOnce form "user_code" | return malformed
  let approve ← match lookupOnce form "decision" with
    | some "approve" => pure true
    | some "deny" => pure false
    | _ => return malformed
  match ← lookup ctx r s typed with
  | .error msg =>
    return page "Connect a device" (s!"<p class=\"error\">{htmlEscape msg}</p>\n" ++ codeForm "")
      .badRequest
  | .ok (code, d) =>
    let need ← approvalLevel ctx d.clientId
    if approve && !s.level.satisfies need then
      return signinRedirect s!"/device?{queryString [("user_code", code)]}" (acr := some need)
    let now ← ctx.clock
    let decision : Store.DeviceStatus :=
      if approve then .approved s.user s.amr s.authTime else .denied
    let applied ← ctx.store.decideDeviceCode code decision now
    let name := (← ctx.store.findUser s.user).map (·.name)
    Audit.log ctx r .deviceDecision (if approve then .success else .refused) (userName := name)
      (detail := if applied then "" else "the code was no longer pending")
    if !applied then
      return page "Connect a device" "<p>That code is no longer waiting.</p>" .badRequest
    if approve then
      return page "Device connected" "<p>You can return to your device now.</p>"
    return page "Device refused" "<p>The device was refused.  You can close this page.</p>"

end Device
end Pyle