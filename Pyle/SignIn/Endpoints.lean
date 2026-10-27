import Pyle.SignIn.Common

/-!
# Signing in and stepping up

The endpoints behind the sign-in page, as JSON over `fetch`:

| | body | answer |
| --- | --- | --- |
| `POST /signin/webauthn/begin` | `{}` or `{"name"}` | request options |
| `POST /signin/webauthn/finish` | `{"credential", "totp"?, "recovery"?, "password"?, "return"?, "acr"?}` | `{"redirect", "amr", "acr"}` |
| `POST /signin/stepup/begin` | `{"userVerification"?}` | request options |
| `POST /signin/stepup/finish` | as `/signin/webauthn/finish` | as `/signin/webauthn/finish` |
| `POST /signin/codes` | `{"name", "password"?, "totp"?, "recovery"?, "return"?, "acr"?}` | as `/signin/webauthn/finish` |

**Passkeys.**  `begin` with no name starts the discoverable flow of DESIGN
§7: no username is asked for, user verification is required, and the
browser must return the user handle.  A passkey's assertion reaches `phr`
on its own, `phrh` from a device-bound credential.

**Security keys and codes.**  `begin` with a name lists that account's
credentials, for a security key that cannot be discovered or does not verify
the user; such an assertion is one factor, and `finish` needs a TOTP code, a
recovery code or a password with it, which makes it `mfa`.  The list is
padded to a fixed length with ids derived from the name, so the answer has the
same shape whether the name exists or not.
`/signin/codes` signs in with two of a password, a TOTP code and a recovery
code (`mfa`); given fewer than two it refuses before checking anything, so a
password alone is never even tried.

**The level asked for.**  A body may name the level the sign-in must reach,
as `acr` (a short name or an identifier, `Acr.ofIdentifier?`); the sign-in
page passes on the one a service asked for.  Every sign-in is at least `mfa`,
so only `phr` and `phrh` can fall short: the code form and a security key
without user verification are refused before any second factor is checked,
and an assertion that verified the user but is not device-bound after, with
`401 stronger_authentication_required` and no session.

**Step-up.**  `/signin/stepup/*` re-authenticates the request's session
(§4) without ending it.  Every finish does the same when the request already
carries a session of the same user, so the sign-in page serves both.

**What is counted.**  Every finish and `/signin/codes` is one attempt
against the rate limiter (§7) and one audit record, successful or not.  A
failure answers `401` and says nothing about which factor was wrong.
-/

namespace Pyle
namespace SignIn

open Http Store Policy
open Lean (Json ToJson toJson)

/-- The second factors a body may carry besides an assertion. -/
structure Extras where
  /-- A TOTP code. -/
  totp : Option String
  /-- A recovery code. -/
  recovery : Option String
  /-- A password. -/
  password : Option String

/-- The second factors in a body; an empty string is no factor. -/
def extrasOf (j : Json) : Extras :=
  let get (k : String) := (strField j k).filter (!·.isEmpty)
  { totp := get "totp", recovery := get "recovery", password := get "password" }

/-- How many second factors a body carries. -/
def Extras.count (e : Extras) : Nat :=
  [e.totp.isSome, e.recovery.isSome, e.password.isSome].count true

/-- The `return` of a body, defaulting to `defaultReturn`; the `400` to
answer if it is not a path on this origin. -/
def returnOf (j : Json) : Except Reply String :=
  match strField j "return" with
  | none => .ok defaultReturn
  | some s => match safeReturn s with
    | some t => .ok t
    | none => .error (badRequest "'return' must be a path on this origin")

/-- Check the second factors of a body for a user: the password first, which
changes nothing; then whether the recovery code is one of the user's, without
spending it; then the TOTP code, which uses up its time step and whose
failures count towards the lock of §7; then the recovery code is spent.  So
TOTP is only tried, and a wrong code only counted, once every other factor
given has checked out: someone who knows neither a password nor a recovery
code cannot lock another user's TOTP.  The factors, or the factor that failed
and why.  A failure that locks TOTP is audited as such. -/
def checkExtras (ctx : Ctx) (r : Req) (user : User) (e : Extras) :
    IO (Except (String × String) (List Factor)) := do
  let mut factors := []
  if let some p := e.password then
    match ← checkPassword ctx (some user.id) p with
    | some f => factors := factors ++ [f]
    | none => return .error ("password", "wrong password, or passwords are off")
  if let some code := e.recovery then
    unless ← recoveryCodeValid ctx user.id code do
      return .error ("recovery", "wrong or spent recovery code")
  if let some code := e.totp then
    match ← checkTotp ctx user.id code r.clientAddress with
    | .ok f => factors := factors ++ [f]
    | .error .notEnrolled => return .error ("totp", "no TOTP secret")
    | .error (.locked _) => return .error ("totp", "TOTP is locked")
    | .error (.wrong lockedUntil) =>
      if lockedUntil.isSome then
        Audit.log ctx r .totpLocked .refused (userName := some user.name) (factor := some "totp")
          (detail := "five wrong codes")
      return .error ("totp", "wrong or reused code")
  if let some code := e.recovery then
    match ← checkRecovery ctx user.id code with
    | some f =>
      factors := factors ++ [f]
      Audit.log ctx r .recoveryCode .success (userName := some user.name)
        (factor := some "recovery")
    | none => return .error ("recovery", "wrong or spent recovery code")
  return .ok factors

/-- The level a body asks the sign-in to reach, `mfa` (anything) if it names
none; the `400` to answer if it names a level pyle does not know. -/
def wantOf (j : Json) : Except Reply Acr :=
  match strField j "acr" with
  | none => .ok .mfa
  | some s => match Acr.ofIdentifier? s with
    | some a => .ok a
    | none => .error (badRequest "'acr' is not a level pyle knows")

/-- The reply to an authentication: `{"redirect", "amr", "acr"}` with the new
session cookie, `acr` being the session's level. -/
def signedIn (ctx : Ctx) (s : Session) (id : String) (ret : String) : IO Reply := do
  let body := Json.mkObj [("redirect", ret), ("amr", toJson s.amr),
    ("acr", s.level.identifier)]
  return Session.setCookie ctx s id (← ctx.clock) (.json body)

/-- What finishing with an authentication came to. -/
structure Concluded where
  /-- The reply, with the new cookie. -/
  reply : Reply
  /-- Whether the request's session was stepped up rather than replaced. -/
  steppedUp : Bool
  /-- The live session the request carried, if establishing a new one ended
  it. -/
  ended : Option Session

/-- Finish with an authentication: step up the request's session if it is the
same user's, otherwise establish a new one (which ends the request's session,
if any).  With `stepUpOnly`, there must be a session to step up, and `none` if
there is not. -/
def conclude (ctx : Ctx) (r : Req) (sa : Authentication) (ret : String)
    (stepUpOnly : Bool) : IO (Option Concluded) := do
  let current ← Session.current ctx r
  if let some s := current then
    if s.user == sa.user then
      if let some (s', id) ← Policy.stepUp ctx s sa then
        return some { reply := ← signedIn ctx s' id ret, steppedUp := true, ended := none }
  if stepUpOnly then return none
  let (s, id) ← Policy.establish ctx r sa
  return some { reply := ← signedIn ctx s id ret, steppedUp := false, ended := current }

/-- Conclude, and only then count the attempts as successes and audit: the
sign-in or step-up with the level it reached, and the session a new sign-in
ended. -/
def concludeAndRecord (ctx : Ctx) (r : Req) (event : Audit.Event) (who : String)
    (sa : Authentication) (ret : String) (stepUpOnly : Bool) (lim : RateLimiter)
    (attempts : List Attempt) : IO Reply := do
  match ← conclude ctx r sa ret stepUpOnly with
  | none =>
    Audit.log ctx r event .failure (userName := some who) (detail := "no session to step up")
    return signInRequired
  | some c =>
    for a in attempts do lim.succeed a
    Audit.log ctx r (if c.steppedUp then .stepUp else event) .success (userName := some who)
      (factor := some (", ".intercalate sa.labels)) (detail := s!"acr {sa.level.identifier}")
    if let some old := c.ended then
      Audit.log ctx r .signOut .success (userName := ← userName ctx old.user)
        (detail := "replaced by a new sign-in")
    return c.reply

/-- `401 second_factor_required`: one factor checked out, and it is not
enough on its own. -/
def secondFactorRequired : Reply :=
  Reply.error .unauthorized "second_factor_required"
    "this authenticator needs a second factor: a TOTP code, a recovery code or a password"

/-- `401 stronger_authentication_required`: the factors checked out, or would
have, but cannot reach `want`; only a passkey can. -/
def strongerRequired (want : Acr) : Reply :=
  Reply.error .unauthorized "stronger_authentication_required" <|
    if want == .phrh then
      "this needs a passkey or security key that verifies you and keeps its key on the device"
    else "this needs a passkey, or a security key that verifies you"

/-- The audit event of a ceremony. -/
def eventOf (purpose : ChallengePurpose) : Audit.Event :=
  if purpose == .stepUp then .stepUp else .signIn

/-- `POST /signin/webauthn/finish` (`purpose = authenticate`) and
`POST /signin/stepup/finish` (`purpose = stepUp`): check the assertion and any
second factors with it, and sign in or step up, if together they reach the
level the body asks for.  Second factors with an assertion that is
phishing-resistant on its own (`phr` or better) are ignored, neither checked
nor counted: they could not raise its level, and a mistyped code must not fail
a passkey.  With any other assertion they are checked — unless even with them
the level asked for is out of reach (above `mfa`), in which case the attempt is
refused before they are touched.

The attempt counts against the client address from the start.  Once the
assertion has said whose account it is, second factors that come with it
count against that account too, as they do at `/signin/codes`: guessing a
password from many addresses with one stolen security key is limited like
guessing it without one. -/
def finishAssertion (purpose : ChallengePurpose) : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let ret ← match returnOf j with
    | .ok t => pure t
    | .error rep => return rep
  let want ← match wantOf j with
    | .ok a => pure a
    | .error rep => return rep
  let some credJ := (j.getObjVal? "credential").toOption | return badRequest "'credential' is missing"
  let resp ← match parseAssertion credJ with
    | .ok a => pure a
    | .error e => return badRequest e
  let stepUpOnly := purpose == .stepUp
  if stepUpOnly && (← Session.current ctx r).isNone then return signInRequired
  let event := eventOf purpose
  let credLabel := "webauthn:" ++ b64 resp.credentialId
  let extras := extrasOf j
  limited ctx r event none fun lim attempt => do
    match ← checkAssertion ctx purpose resp with
    | .error e =>
      Audit.log ctx r event .failure (factor := some credLabel) (detail := e.reason)
      return authenticationFailed
    | .ok ca =>
      -- A phishing-resistant assertion stands alone, at its own level;
      -- any other reaches `mfa` with a second factor, and nothing without.
      let pr := decide ca.factor.PhishingResistant
      let extras : Extras :=
        if pr then { totp := none, recovery := none, password := none } else extras
      let best := if pr then Policy.level [ca.factor] else .mfa
      unless best.satisfies want do
        Audit.log ctx r event .failure (userName := some ca.user.name)
          (factor := some credLabel) (detail := s!"{want.identifier} asked for")
        return strongerRequired want
      if !pr && extras.count == 0 then
        Audit.log ctx r event .failure (userName := some ca.user.name)
          (factor := some credLabel) (detail := "second factor required")
        return secondFactorRequired
      let mut attempts := [attempt]
      if extras.count > 0 then
        -- The address was counted by `limited` already; the client key here
        -- is the account's own, so the address is not counted twice.
        match ← lim.tryAcquire (some ca.user.name) ("account:" ++ ca.user.name)
            (← ctx.clock) with
        | .error wait =>
          Audit.log ctx r event .refused (userName := some ca.user.name)
            (detail := "rate limited")
          return rateLimited wait
        | .ok a => attempts := attempts ++ [a]
      match ← checkExtras ctx r ca.user extras with
      | .error (f, why) =>
        Audit.log ctx r event .failure (userName := some ca.user.name) (factor := some f)
          (detail := why)
        return authenticationFailed
      | .ok more =>
        let some sa := Authentication.ofFactors (ca.factor :: more)
          | Audit.log ctx r event .failure (userName := some ca.user.name)
              (factor := some credLabel) (detail := "second factor required")
            return secondFactorRequired
        unless sa.level.satisfies want do
          Audit.log ctx r event .failure (userName := some ca.user.name)
            (factor := some credLabel) (detail := s!"{want.identifier} asked for")
          return strongerRequired want
        concludeAndRecord ctx r event ca.user.name sa ret stepUpOnly lim attempts

/-- A user name as typed: trimmed and lower-cased, as names are stored. -/
def normaliseName (s : String) : String := s.trimAscii.toString.toLower

/-- How many credential ids a named begin lists, at least. -/
def namedAllowCount : Nat := 8

/-- The credential list of a named begin: the account's credential ids, then
padding ids (`Secrets.paddingCredentialId`) up to `namedAllowCount`, and no
transports.  An unknown name, or one without credentials, gets padding only,
the same every time; since padding ids have the lengths real ones have, the
answer has the same shape whether the name exists or not (§7).  An account
with more than `namedAllowCount` credentials is listed whole, which says that
it exists; few have that many. -/
def namedAllowList (rootKey : ByteArray) (name : String) (ids : List ByteArray) : List Json :=
  let padding := (List.range (namedAllowCount - ids.length)).map fun i =>
    Secrets.paddingCredentialId rootKey name i
  (ids ++ padding).map (descriptor · [])

/-- `POST /signin/webauthn/begin`: options for a passkey (`{}`) or for a named
account's security keys (`{"name"}`). -/
def beginSignIn : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  match (strField j "name").map normaliseName |>.filter (!·.isEmpty) with
  | none =>
    let ch ← match ← newChallenge ctx r .authenticate none with
      | .ok ch => pure ch
      | .error rep => return rep
    return .json (requestOptions ctx ch [] "required")
  | some name =>
    let user ← ctx.store.findUserByName name
    let user := user.filter (!·.disabled)
    let creds ← match user with
      | some u => pure (← ctx.store.listCredentials u.id).toList
      | none => pure []
    let ch ← match ← newChallenge ctx r .authenticate
        ((if creds.isEmpty then none else user).map (·.id)) with
      | .ok ch => pure ch
      | .error rep => return rep
    return .json (requestOptions ctx ch (namedAllowList ctx.rootKey name (creds.map (·.id)))
      "discouraged")

/-- `POST /signin/stepup/begin`: options for re-authenticating the request's
session with one of its user's credentials.  User verification is required
unless the body asks for `"discouraged"`, for a security key that has none
(it then needs a second factor at finish). -/
def beginStepUp : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let s ← match ← requireSession ctx r with
    | .ok s => pure s
    | .error rep => return rep
  let uv := if strField j "userVerification" == some "discouraged" then "discouraged"
    else "required"
  let creds ← ctx.store.listCredentials s.user
  let ch ← match ← newChallenge ctx r .stepUp (some s.user) with
    | .ok ch => pure ch
    | .error rep => return rep
  return .json (requestOptions ctx ch (creds.toList.map fun c => descriptor c.id c.transports) uv)

/-- `POST /signin/codes`: sign in, or step up, with two of a password, a TOTP
code and a recovery code.  Fewer than two, or a body asking for more than
`mfa`, is refused before anything is checked. -/
def signInWithCodes : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let ret ← match returnOf j with
    | .ok t => pure t
    | .error rep => return rep
  let some name := (strField j "name").map normaliseName |>.filter (!·.isEmpty)
    | return badRequest "'name' is missing"
  let want ← match wantOf j with
    | .ok a => pure a
    | .error rep => return rep
  let extras := extrasOf j
  if extras.count < 2 then
    return Reply.error .badRequest "two_factors_required"
      "two of a password, a TOTP code and a recovery code are needed"
  unless Acr.mfa.satisfies want do return strongerRequired want
  limited ctx r .signIn (some name) fun lim attempt => do
    let user ← ctx.store.findUserByName name
    let some user := user.filter (!·.disabled)
      | if let some p := extras.password then discard <| checkPassword ctx none p
        Audit.log ctx r .signIn .failure (userName := some name) (detail := "unknown user")
        return authenticationFailed
    match ← checkExtras ctx r user extras with
    | .error (f, why) =>
      Audit.log ctx r .signIn .failure (userName := some name) (factor := some f) (detail := why)
      return authenticationFailed
    | .ok factors =>
      let some sa := Authentication.ofFactors factors
        | Audit.log ctx r .signIn .failure (userName := some name)
            (detail := "the factors do not satisfy the policy")
          return authenticationFailed
      unless sa.level.satisfies want do
        Audit.log ctx r .signIn .failure (userName := some name)
          (detail := s!"{want.identifier} asked for")
        return strongerRequired want
      concludeAndRecord ctx r .signIn name sa ret false lim [attempt]

end SignIn
end Pyle