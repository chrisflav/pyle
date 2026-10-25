import PyleTests.Token

/-!
# The device authorization grant

RFC 8628 end to end through `Server.route`: a client asks for codes, polls
while nobody has decided (`authorization_pending`, and `slow_down` when it
polls too fast), a user with a phishing-resistant session approves or denies
on `/device`, and the client gets its tokens once, or `access_denied`, or
`expired_token`.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc

/-- Ask for device codes as the public client `cli`. -/
def deviceCodes (ctx : Ctx) : IO Reply :=
  postForm ctx "/device_authorization" [("client_id", "cli"), ("scope", "openid groups")]

/-- Poll with a device code as `cli`. -/
def pollDevice (ctx : Ctx) (deviceCode : String) : IO Reply :=
  postForm ctx "/token" [("grant_type", Device.grantType), ("device_code", deviceCode),
    ("client_id", "cli")]

/-- User codes. -/
def userCodeTests : IO Unit := do
  group "device: user codes"
  let codes ← (List.range 50).mapM fun _ => Device.newUserCode
  check "eight characters of the base-20 alphabet" (codes.all fun c =>
    c.length == 8 && c.all Device.alphabet.contains)
  checkEq "shown as XXXX-XXXX" (Device.display "BCDFGHJK") "BCDF-GHJK"
  checkEq "typed case-blind, separators dropped" (Device.normalise "bcdf ghjk") (some "BCDFGHJK")
  checkEq "and with the dash" (Device.normalise "BCDF-GHJK") (some "BCDFGHJK")
  checkEq "too short is no code" (Device.normalise "BCDF") none
  checkEq "vowels are not in the alphabet" (Device.normalise "AEIOUBCD") none

/-- The flow. -/
def deviceFlowTests : IO Unit := withCtx fun ctx clock => do
  group "device: flow"
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let (appSecret, _) ← addClients ctx
  let r ← deviceCodes ctx
  checkEq "device authorization answers" r.status.toCode 200
  let some deviceCode := jsonStr r "device_code" | check "a device code" false
  let some userCode := jsonStr r "user_code" | check "a user code" false
  checkEq "the verification URI" (jsonStr r "verification_uri") (some s!"{issuer}/device")
  checkEq "and the complete one" (jsonStr r "verification_uri_complete")
    (some s!"{issuer}/device?user_code={userCode}")
  checkEq "the interval" ((bodyJson r).getObjValAs? Nat "interval" |>.toOption)
    (some ctx.config.devicePollSeconds)
  checkEq "the lifetime" ((bodyJson r).getObjValAs? Nat "expires_in" |>.toOption)
    (some ctx.config.deviceCodeSeconds)
  let unknown ← postForm ctx "/device_authorization" [("client_id", "nobody")]
  checkEq "an unknown client is refused" (jsonStr unknown "error") (some "invalid_client")
  -- Polling before anyone decides.
  checkEq "pending" (jsonStr (← pollDevice ctx deviceCode) "error") (some "authorization_pending")
  checkEq "too fast: slow_down" (jsonStr (← pollDevice ctx deviceCode) "error") (some "slow_down")
  clock.modify (· + ctx.config.devicePollSeconds)
  checkEq "slow_down adds five seconds to the interval" (jsonStr (← pollDevice ctx deviceCode)
    "error") (some "slow_down")
  clock.modify (· + ctx.config.devicePollSeconds + 10)
  checkEq "waiting the grown interval is pending again" (jsonStr (← pollDevice ctx deviceCode)
    "error") (some "authorization_pending")
  -- The page needs a phishing-resistant session.
  let page := s!"/device?{queryString [("user_code", userCode)]}"
  let r ← get ctx page
  check "without a session the page sends to sign in" ((location r).startsWith "/signin?")
  checkEq "asking for a passkey" (param (location r) "acr") (some "phr")
  checkEq "and back to the code" (param (location r) "return") (some page)
  let weak ← weakFor ctx alice
  let r ← get ctx page weak
  checkEq "a session without a passkey is sent to sign in too" (param (location r) "acr")
    (some "phr")
  let cookie ← signedIn ctx alice
  let r ← get ctx page cookie
  checkEq "with a passkey the page answers" r.status.toCode 200
  check "naming the client" ((r.bodyText.splitOn "A CLI").length > 1)
  check "and offering a decision" ((r.bodyText.splitOn "value=\"approve\"").length > 1)
  let r ← get ctx "/device?user_code=BBBB-BBBB" cookie
  checkEq "an unknown code is refused" r.status.toCode 400
  -- Approving.
  let crossSite ← postForm ctx "/device" [("user_code", userCode), ("decision", "approve")]
    [("Origin", "https://evil.example")] (cookie := some cookie)
  checkEq "a cross-site approval is refused" crossSite.status.toCode 403
  let r ← postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some cookie)
  checkEq "approving answers" r.status.toCode 200
  clock.modify (· + ctx.config.devicePollSeconds)
  let t ← pollDevice ctx deviceCode
  checkEq "the poll gets tokens" t.status.toCode 200
  let access := (jsonStr t "access_token").getD ""
  let roots ← Token.publishedRoots ctx.store
  checkEq "an access token for alice, with the approving session's amr"
    ((Token.verify roots "cli" (← clock.get) access).toOption.map fun i => (i.user, i.amr))
    (some ("alice", ["hwk", "user"]))
  check "and a refresh token" (jsonStr t "refresh_token").isSome
  check "and an ID token" (jsonStr t "id_token").isSome
  clock.modify (· + ctx.config.devicePollSeconds)
  checkEq "a device code yields tokens once" (jsonStr (← pollDevice ctx deviceCode) "error")
    (some "expired_token")
  let log ← Audit.entries ctx.store
  check "the decision is audited" (log.any (·.event == "device-decision"))
  -- Denying.
  let r ← deviceCodes ctx
  let dc := (jsonStr r "device_code").getD ""
  let uc := (jsonStr r "user_code").getD ""
  discard <| postForm ctx "/device" [("user_code", uc), ("decision", "deny")] sameOrigin
    (cookie := some cookie)
  clock.modify (· + ctx.config.devicePollSeconds)
  checkEq "a denied code: access_denied" (jsonStr (← pollDevice ctx dc) "error")
    (some "access_denied")
  -- Another client cannot collect.
  let r ← deviceCodes ctx
  let dc := (jsonStr r "device_code").getD ""
  let uc := (jsonStr r "user_code").getD ""
  discard <| postForm ctx "/device" [("user_code", uc), ("decision", "approve")] sameOrigin
    (cookie := some cookie)
  clock.modify (· + ctx.config.devicePollSeconds)
  let stolen ← postForm ctx "/token" [("grant_type", Device.grantType), ("device_code", dc),
    ("client_id", "nobody")]
  checkEq "an unknown client cannot poll" (jsonStr stolen "error") (some "invalid_client")
  let other ← postForm ctx "/token" [("grant_type", Device.grantType), ("device_code", dc)]
    (basic "app" appSecret)
  checkEq "nor another client" (jsonStr other "error") (some "invalid_grant")
  checkEq "whose poll destroys nothing: the right client still collects"
    (← pollDevice ctx dc).status.toCode 200
  -- Expiry.
  let r ← deviceCodes ctx
  let dc := (jsonStr r "device_code").getD ""
  clock.modify (· + ctx.config.deviceCodeSeconds)
  checkEq "an expired code: expired_token" (jsonStr (← pollDevice ctx dc) "error")
    (some "expired_token")

/-- The device grant. -/
def deviceGrantTests : IO Unit := do
  userCodeTests
  deviceFlowTests

end PyleTests