import Pyle.SignIn.Common

/-!
# Managing an account

What a signed-in user can do to their own account (DESIGN §1, §3, §4), as
JSON over `fetch`.  Every change that adds or removes a way in, or renames
one, needs a step-up within the last five minutes (`requireStepUp`), and
answers `403 step_up_required` otherwise, which the account page meets by
running a step-up and trying again.  Ending a session needs only the session:
taking access away is never what an attacker with a stolen cookie wants to be
stopped from.

| | body | answer |
| --- | --- | --- |
| `POST /account/authenticators/register/begin` | `{}` | creation options |
| `POST /account/authenticators/register/finish` | `{"credential", "name"?}` | `201 {"id"}` |
| `POST /account/authenticators/rename` | `{"id", "name"}` | `204` |
| `POST /account/authenticators/remove` | `{"id"}` | `204`, or `409` |
| `POST /account/totp/begin` | `{}` | `{"secret", "uri", "pending"}` |
| `POST /account/totp/confirm` | `{"pending", "code"}` | `204` |
| `POST /account/totp/remove` | `{}` | `204`, or `409` |
| `POST /account/recovery-codes` | `{}` | `{"codes"}` |
| `POST /account/password` | `{"password"}` | `204` |
| `POST /account/password/remove` | `{}` | `204` |
| `POST /account/sessions/end` | `{"handle"}` | `204` |

**At least two.**  Removing a credential or the TOTP secret is refused with
`409` when it would leave fewer than two authenticators (§1); the store makes
the count and the delete one transaction.

**TOTP enrolment** takes two requests and remembers nothing in between: the
new secret goes to the browser, shown as base32 and as an `otpauth://` URI,
and also sealed for this user with the time it was issued
(`Secrets.sealPending`).  The browser hands the sealed value back with the
first code from the app; only a code that verifies against it stores the
secret, and it must come within ten minutes.  The code's step is recorded as
used, so it cannot then be used to sign in.

**Recovery codes** are generated ten at a time, replace the old ones, and are
in the answer once; the database keeps only their HMACs.

**Passwords**, when the deployment allows them, are at least twelve
characters.  The breached-password check DESIGN §3 mentions needs a list pyle
does not ship; it is left to a later round.
-/

namespace Pyle
namespace Account

open Http Store SignIn
open Lean (Json toJson)

/-- Run `act` with the session if it authenticated within the step-up
window, and the body as JSON. -/
def withStepUp (ctx : Ctx) (r : Req) (act : Session → Json → IO Reply) : IO Reply := do
  let s ← match ← requireStepUp ctx r with
    | .ok s => pure s
    | .error rep => return rep
  match jsonBody r with
  | .ok j => act s j
  | .error rep => return rep

/-- The account a session belongs to. -/
def userOf (ctx : Ctx) (s : Session) : IO User := do
  let some u ← ctx.store.findUser s.user | throw (.userError "the session's user is gone")
  return u

/-- A credential id from a body. -/
def idOf (j : Json) : Except Reply ByteArray :=
  (bytesField j "id").mapError badRequest

/-- `POST /account/authenticators/register/begin`. -/
def registerBegin : Handler := fun ctx r => withStepUp ctx r fun s _ => do
  let u ← userOf ctx s
  let creds ← ctx.store.listCredentials u.id
  let ch ← newChallenge ctx .register (some u.id)
  return .json (creationOptions ctx ch u.handle u.name
    (creds.toList.map fun c => descriptor c.id c.transports) "preferred" "preferred")

/-- `POST /account/authenticators/register/finish`. -/
def registerFinish : Handler := fun ctx r => withStepUp ctx r fun s j => do
  let some credJ := (j.getObjVal? "credential").toOption | return badRequest "'credential' is missing"
  let reg ← match parseRegistration credJ with
    | .ok x => pure x
    | .error e => return badRequest e
  let u ← userOf ctx s
  let refuse (why : String) : IO Reply := do
    Audit.log ctx r .register .failure (userName := some u.name) (detail := why)
    return Reply.error .badRequest "registration_failed" "the authenticator could not be registered"
  let some (challenge, ch) ← consumeRegistrationChallenge ctx reg
    | refuse "unknown or expired challenge"
  if ch.user != some u.id then return ← refuse "challenge issued to someone else"
  match ← verifyNewCredential ctx challenge reg (requireUserVerification := false) with
  | .error why => refuse why
  | .ok c =>
    if (← ctx.store.findCredential c.id).isSome then
      Audit.log ctx r .register .failure (userName := some u.name) (detail := "already registered")
      return Reply.error .conflict "already_registered" "this authenticator is already registered"
    let n := (← ctx.store.listCredentials u.id).size
    let name := credentialName (strField j "name") s!"authenticator {n + 1}"
    ctx.store.addCredential (credentialRow c u.id name reg.transports (← ctx.clock))
    Audit.log ctx r .register .success (userName := some u.name)
      (factor := some ("webauthn:" ++ b64 c.id))
    return .json (Json.mkObj [("id", b64 c.id)]) .created

/-- `POST /account/authenticators/rename`. -/
def rename : Handler := fun ctx r => withStepUp ctx r fun s j => do
  let id ← match idOf j with
    | .ok id => pure id
    | .error rep => return rep
  let some name := strField j "name" | return badRequest "'name' is missing"
  let name := credentialName (some name) ""
  if name.isEmpty then return badRequest "the name is empty"
  if ← ctx.store.renameCredential s.user id name then
    Audit.log ctx r .userChanged .success (userName := ← userName ctx s.user)
      (factor := some ("webauthn:" ++ b64 id)) (detail := "authenticator renamed")
    return .noContent
  return Reply.error .notFound "not_found" "no such authenticator"

/-- `409`, for a removal that would leave fewer than two authenticators. -/
def lastTwo : Reply :=
  Reply.error .conflict "last_authenticators"
    "an account keeps at least two authenticators; add another before removing this one"

/-- `POST /account/authenticators/remove`. -/
def remove : Handler := fun ctx r => withStepUp ctx r fun s j => do
  let id ← match idOf j with
    | .ok id => pure id
    | .error rep => return rep
  let name ← userName ctx s.user
  let factor := some ("webauthn:" ++ b64 id)
  match ← ctx.store.findCredential id with
  | some c =>
    if c.user != s.user then return Reply.error .notFound "not_found" "no such authenticator"
    if ← ctx.store.removeCredential s.user id then
      Audit.log ctx r .removeAuthenticator .success (userName := name) (factor := factor)
      return .noContent
    Audit.log ctx r .removeAuthenticator .refused (userName := name) (factor := factor)
      (detail := "would leave fewer than two authenticators")
    return lastTwo
  | none => return Reply.error .notFound "not_found" "no such authenticator"

/-- How long a TOTP secret being enrolled may wait for its first code. -/
def enrolmentSeconds : Nat := 600

/-- The issuer an authenticator app shows next to the account. -/
def totpIssuer (ctx : Ctx) : String := ctx.config.rpId

/-- The base32 of a secret, without padding, as people type it. -/
def base32Text (b : ByteArray) : String :=
  String.ofList ((Factor.base32Encode b).toList.filter (· != '='))

/-- `POST /account/totp/begin`: a new secret, not yet stored. -/
def totpBegin : Handler := fun ctx r => withStepUp ctx r fun s _ => do
  let u ← userOf ctx s
  let secret ← Factor.Totp.generateSecret
  let pending ← Secrets.sealPending ctx.rootKey u.id secret (← ctx.clock)
  return .json (Json.mkObj [("secret", base32Text secret),
    ("uri", Factor.Totp.uri (totpIssuer ctx) u.name secret), ("pending", b64 pending)])

/-- `POST /account/totp/confirm`: store the secret once a code from it
verifies.  Counted against the rate limiter, since it checks a code. -/
def totpConfirm : Handler := fun ctx r => withStepUp ctx r fun s j => do
  let u ← userOf ctx s
  let pending ← match bytesField j "pending" with
    | .ok p => pure p
    | .error e => return badRequest e
  let some code := strField j "code" | return badRequest "'code' is missing"
  limited ctx r .register (some u.name) fun lim attempt => do
    let now ← ctx.clock
    let some (secret, issued) := Secrets.openPending ctx.rootKey u.id pending
      | return badRequest "'pending' is not a secret issued to this account"
    if issued + enrolmentSeconds < now then
      return Reply.error .badRequest "expired" "start the set-up again"
    let some step := Factor.Totp.verify secret now (Policy.normaliseCode code) none
      | Audit.log ctx r .register .failure (userName := some u.name) (factor := some "totp")
          (detail := "wrong first code")
        return Reply.error .badRequest "invalid_code" "the code does not match; try the next one"
    lim.succeed attempt
    ctx.store.setTotp u.id (← Secrets.sealTotp ctx.rootKey u.id secret) now
    discard <| ctx.store.acceptTotpStep u.id step now
    Audit.log ctx r .register .success (userName := some u.name) (factor := some "totp")
    return .noContent

/-- `POST /account/totp/remove`. -/
def totpRemove : Handler := fun ctx r => withStepUp ctx r fun s _ => do
  let name ← userName ctx s.user
  if (← ctx.store.findTotp s.user).isNone then
    return Reply.error .notFound "not_found" "there is no TOTP secret"
  if ← ctx.store.removeTotp s.user then
    Audit.log ctx r .removeAuthenticator .success (userName := name) (factor := some "totp")
    return .noContent
  Audit.log ctx r .removeAuthenticator .refused (userName := name) (factor := some "totp")
    (detail := "would leave fewer than two authenticators")
  return lastTwo

/-- `POST /account/recovery-codes`: ten new codes, replacing the old ones. -/
def recoveryCodes : Handler := fun ctx r => withStepUp ctx r fun s _ => do
  let codes ← Factor.RecoveryCode.generate
  let key := Secrets.recoveryKey ctx.rootKey
  ctx.store.setRecoveryCodes s.user (codes.map (Factor.RecoveryCode.digest key))
  Audit.log ctx r .register .success (userName := ← userName ctx s.user)
    (factor := some "recovery") (detail := "recovery codes replaced")
  return .json (Json.mkObj [("codes", toJson codes)])

/-- The shortest password accepted, in characters. -/
def minPasswordLength : Nat := 12

/-- The longest, so that hashing one costs a bounded amount. -/
def maxPasswordLength : Nat := 1024

/-- `403`, when the deployment does not allow passwords. -/
def passwordsOff : Reply :=
  Reply.error .forbidden "passwords_disabled" "this deployment does not use passwords"

/-- `POST /account/password`: set or replace the password. -/
def setPassword : Handler := fun ctx r => withStepUp ctx r fun s j => do
  if !ctx.config.allowPasswords then return passwordsOff
  let some pw := strField j "password" | return badRequest "'password' is missing"
  if pw.length < minPasswordLength then
    return Reply.error .badRequest "password_too_short"
      s!"a password has at least {minPasswordLength} characters"
  if pw.length > maxPasswordLength then
    return Reply.error .badRequest "password_too_long"
      s!"a password has at most {maxPasswordLength} characters"
  ctx.store.setPassword s.user (← Factor.Password.hash pw) (← ctx.clock)
  Audit.log ctx r .register .success (userName := ← userName ctx s.user)
    (factor := some "password")
  return .noContent

/-- `POST /account/password/remove`. -/
def removePassword : Handler := fun ctx r => withStepUp ctx r fun s _ => do
  if ← ctx.store.removePassword s.user then
    Audit.log ctx r .removeAuthenticator .success (userName := ← userName ctx s.user)
      (factor := some "password")
    return .noContent
  return Reply.error .notFound "not_found" "there is no password"

/-- `POST /account/sessions/end`: end one of the user's sessions by its
handle.  Ending the request's own session also clears its cookie. -/
def endSession : Handler := fun ctx r => do
  let s ← match ← requireSession ctx r with
    | .ok s => pure s
    | .error rep => return rep
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let some handle := strField j "handle" | return badRequest "'handle' is missing"
  if ← Session.terminate ctx s.user handle then
    Audit.log ctx r .signOut .success (userName := ← userName ctx s.user)
      (detail := "ended from the session list")
    return if handle == s.handle then Reply.noContent.clearSession else .noContent
  return Reply.error .notFound "not_found" "no such session"

end Account
end Pyle