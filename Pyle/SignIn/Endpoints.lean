import Pyle.SignIn.Common

/-!
# Signing in and stepping up

The endpoints behind the sign-in page, as JSON over `fetch`:

| | body | answer |
| --- | --- | --- |
| `POST /signin/webauthn/begin` | `{}` or `{"name"}` | request options |
| `POST /signin/webauthn/finish` | `{"credential", "totp"?, "recovery"?, "password"?, "return"?}` | `{"redirect", "amr", "acr"}` |
| `POST /signin/stepup/begin` | `{"userVerification"?}` | request options |
| `POST /signin/stepup/finish` | as `/signin/webauthn/finish` | as `/signin/webauthn/finish` |
| `POST /signin/codes` | `{"name", "password"?, "totp"?, "recovery"?, "return"?}` | as `/signin/webauthn/finish` |

**Passkeys.**  `begin` with no name starts the discoverable flow of DESIGN
§7: no username is asked for, user verification is required, and the
browser must return the user handle.  A passkey's assertion is a strong
authentication on its own.

**Security keys and codes.**  `begin` with a name lists that account's
credentials, for a security key that cannot be discovered or does not verify
the user; such an assertion is one factor, and `finish` needs a TOTP code, a
recovery code or a password with it.  An unknown name gets a decoy credential
id, the same each time, so the answer does not say which names exist.
`/signin/codes` signs in with two of a password, a TOTP code and a recovery
code; given fewer than two it refuses before checking anything, so a
password alone is never even tried.

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
changes nothing; then the TOTP code, which uses up its time step; then the
recovery code, which is spent.  The factors, or the factor that failed and
why.  A failure that locks TOTP is audited as such. -/
def checkExtras (ctx : Ctx) (r : Req) (user : User) (e : Extras) :
    IO (Except (String × String) (List Factor)) := do
  let mut factors := []
  if let some p := e.password then
    match ← checkPassword ctx (some user.id) p with
    | some f => factors := factors ++ [f]
    | none => return .error ("password", "wrong password, or passwords are off")
  if let some code := e.totp then
    match ← checkTotp ctx user.id code with
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

/-- The reply to a strong authentication: `{"redirect", "amr", "acr"}` with
the new session cookie. -/
def signedIn (ctx : Ctx) (s : Session) (id : String) (ret : String) : IO Reply := do
  let body := Json.mkObj [("redirect", ret), ("amr", toJson s.amr),
    ("acr", Policy.acr s.amr)]
  return Session.setCookie ctx s id (← ctx.clock) (.json body)

/-- Finish with a strong authentication: step up the request's session if it
is the same user's, otherwise establish a new one (which ends the request's
session, if any).  With `stepUpOnly`, there must be a session to step up. -/
def conclude (ctx : Ctx) (r : Req) (sa : StrongAuthentication) (ret : String)
    (stepUpOnly : Bool) : IO Reply := do
  match ← Session.current ctx r with
  | some s =>
    if s.user == sa.user then
      match ← Policy.stepUp ctx s sa with
      | some (s', id) => return ← signedIn ctx s' id ret
      | none => if stepUpOnly then return signInRequired
    else if stepUpOnly then return signInRequired
  | none => if stepUpOnly then return signInRequired
  let (s, id) ← Policy.establish ctx r sa
  signedIn ctx s id ret

/-- `401 second_factor_required`: one factor checked out, and it is not
enough on its own. -/
def secondFactorRequired : Reply :=
  Reply.error .unauthorized "second_factor_required"
    "this authenticator needs a second factor: a TOTP code, a recovery code or a password"

/-- The audit event of a ceremony. -/
def eventOf (purpose : ChallengePurpose) : Audit.Event :=
  if purpose == .stepUp then .stepUp else .signIn

/-- `POST /signin/webauthn/finish` (`purpose = authenticate`) and
`POST /signin/stepup/finish` (`purpose = stepUp`): check the assertion and any
second factors with it, and sign in or step up. -/
def finishAssertion (purpose : ChallengePurpose) : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let ret ← match returnOf j with
    | .ok t => pure t
    | .error rep => return rep
  let some credJ := (j.getObjVal? "credential").toOption | return badRequest "'credential' is missing"
  let resp ← match parseAssertion credJ with
    | .ok a => pure a
    | .error e => return badRequest e
  let stepUpOnly := purpose == .stepUp
  if stepUpOnly && (← Session.current ctx r).isNone then return signInRequired
  let event := eventOf purpose
  let credLabel := "webauthn:" ++ b64 resp.credentialId
  limited ctx r event none fun lim attempt => do
    match ← checkAssertion ctx purpose resp with
    | .error e =>
      Audit.log ctx r event .failure (factor := some credLabel) (detail := e.reason)
      return authenticationFailed
    | .ok ca =>
      match ← checkExtras ctx r ca.user (extrasOf j) with
      | .error (f, why) =>
        Audit.log ctx r event .failure (userName := some ca.user.name) (factor := some f)
          (detail := why)
        return authenticationFailed
      | .ok more =>
        let some sa := StrongAuthentication.ofFactors (ca.factor :: more)
          | Audit.log ctx r event .failure (userName := some ca.user.name)
              (factor := some credLabel) (detail := "second factor required")
            return secondFactorRequired
        lim.succeed attempt
        Audit.log ctx r event .success (userName := some ca.user.name)
          (factor := some (", ".intercalate sa.labels))
        conclude ctx r sa ret stepUpOnly

/-- A user name as typed: trimmed and lower-cased, as names are stored. -/
def normaliseName (s : String) : String := s.trimAscii.toString.toLower

/-- `POST /signin/webauthn/begin`: options for a passkey (`{}`) or for a named
account's security keys (`{"name"}`). -/
def beginSignIn : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  match (strField j "name").map normaliseName |>.filter (!·.isEmpty) with
  | none =>
    let ch ← newChallenge ctx .authenticate none
    return .json (requestOptions ctx ch [] "required")
  | some name =>
    let user ← ctx.store.findUserByName name
    let user := user.filter (!·.disabled)
    let creds ← match user with
      | some u => pure (← ctx.store.listCredentials u.id).toList
      | none => pure []
    let allow := if creds.isEmpty then [descriptor (Secrets.decoyCredentialId ctx.rootKey name) []]
      else creds.map fun c => descriptor c.id c.transports
    let ch ← newChallenge ctx .authenticate ((if creds.isEmpty then none else user).map (·.id))
    return .json (requestOptions ctx ch allow "discouraged")

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
  let ch ← newChallenge ctx .stepUp (some s.user)
  return .json (requestOptions ctx ch (creds.toList.map fun c => descriptor c.id c.transports) uv)

/-- `POST /signin/codes`: sign in, or step up, with two of a password, a TOTP
code and a recovery code. -/
def signInWithCodes : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let ret ← match returnOf j with
    | .ok t => pure t
    | .error rep => return rep
  let some name := (strField j "name").map normaliseName |>.filter (!·.isEmpty)
    | return badRequest "'name' is missing"
  let extras := extrasOf j
  if extras.count < 2 then
    return Reply.error .badRequest "two_factors_required"
      "two of a password, a TOTP code and a recovery code are needed"
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
      let some sa := StrongAuthentication.ofFactors factors
        | Audit.log ctx r .signIn .failure (userName := some name)
            (detail := "the factors do not satisfy the policy")
          return authenticationFailed
      lim.succeed attempt
      Audit.log ctx r .signIn .success (userName := some name)
        (factor := some (", ".intercalate sa.labels))
      conclude ctx r sa ret false

end SignIn
end Pyle