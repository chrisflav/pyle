import Pyle.SignIn.Common

/-!
# Invitations

Accounts are created by an administrator or by invitation, never by sign-up
(DESIGN, non-goals).  `pyle invite <name>` stores an invitation under the
SHA-256 of a random token and prints `<issuer>/invite/<token>`; whoever opens
that link registers the account's first way in there.

| | body | answer |
| --- | --- | --- |
| `POST /invite/<token>/begin` | `{"kind"?}` | creation options |
| `POST /invite/<token>/finish` | `{"credential", "name"?}` | `201 {"name", "acr"}` |
| `POST /invite/<token>/password` | `{"password"}` | `201 {"name", "acr"}` |

The first way in may be a passkey, the default `kind`, asked for as a
discoverable credential that verifies the user; a security key touched
without a PIN (`"kind": "security-key"`: not discoverable, user verification
only preferred); or, where the deployment allows passwords, a password.  The
latter two sign in alone only at `sfa` (DESIGN §1); the answer's `acr` is the
strongest level the new account can reach (`Acr.Capabilities.level`), which
the page shows, and the account page keeps asking for a passkey.

The account does not exist until its first factor is stored, and the
invitation is consumed in the same transaction (`Store.redeemInvitation`), so
an invitation creates at most one account and a registration that fails
leaves it usable.  The page then sends the person on to `/signin` to sign in,
so that the session comes from a checked factor like every other
(`Policy`).

The account's WebAuthn user handle has to be in the creation options, before
the account exists.  It is derived from the registration challenge under a
key of its own (`Secrets.invitationHandle`), so nothing needs remembering
between `begin` and `finish`.
-/

namespace Pyle
namespace SignIn

open Http Store
open Lean (Json)

/-- The length of an invitation token, in bytes. -/
def invitationTokenBytes : Nat := 32

/-- Parse a lifetime such as `7d`, `12h`, `30m` or `90s` into seconds. -/
def parseDuration (s : String) : Option Nat := do
  let unit ← s.toList.getLast?
  let n ← (String.ofList s.toList.dropLast).toNat?
  let scale ← match unit with
    | 'd' => some 86400
    | 'h' => some 3600
    | 'm' => some 60
    | 's' => some 1
    | _ => none
  guard (n > 0)
  return n * scale

/-- Issue an invitation for a new account, valid for `ttl` seconds; the URL to
hand to the person.  Fails if the name is invalid or already taken.  Only the
token's hash is stored. -/
def createInvitation (store : Store) (issuer name : String) (groups : List String)
    (ttl now : Nat) (createdBy : String := "cli") : IO String := do
  unless validUserName name do
    throw (.userError s!"'{name}' is not a valid user name (lower-case letters, digits, \
      '-', '_' and '.', at most 64)")
  if (← store.findUserByName name).isSome then
    throw (.userError s!"there is already a user named '{name}'")
  let token ← Crypto.randomBytes invitationTokenBytes.toUSize
  store.addInvitation (.of token)
    { userName := name, groups, createdBy, created := now, expires := now + ttl }
  return s!"{issuer}/invite/{b64 token}"

/-- The hash of the token a request's path names, if it is one. -/
def tokenHashOf (r : Req) : Option SecretHash := do
  let t ← r.param "token"
  let b ← Encoding.Base64Url.decode t
  guard (b.size == invitationTokenBytes)
  return .of b

/-- The live invitation a request's path names. -/
def invitationOf (ctx : Ctx) (r : Req) : IO (Option (SecretHash × Invitation)) := do
  let some h := tokenHashOf r | return none
  return (← ctx.store.findInvitation h (← ctx.clock)).map (h, ·)

/-- `404` for an invitation that does not exist or has expired. -/
def noInvitation : Reply :=
  Reply.error .notFound "not_found" "this invitation does not exist or has expired"

/-- `POST /invite/<token>/begin`: creation options for the invited account's
first credential — a passkey, or with `"kind": "security-key"` a security key
that need not be discoverable or verify the user.  Counted against the rate
limiter, since it tests a token. -/
def beginInvitation : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let securityKey := strField j "kind" == some "security-key"
  limited ctx r .invitationUsed none fun lim attempt => do
    let some (_, inv) ← invitationOf ctx r | return noInvitation
    lim.succeed attempt
    let ch ← match ← newChallenge ctx r .register none with
      | .ok ch => pure ch
      | .error rep => return rep
    let handle := Secrets.invitationHandle ctx.rootKey ch
    let (residentKey, uv) :=
      if securityKey then ("discouraged", "preferred") else ("required", "required")
    return .json (creationOptions ctx ch handle inv.userName [] residentKey uv)

/-- The `201` of a redeemed invitation: the account's name and the strongest
level it can reach. -/
def invitationRedeemed (ctx : Ctx) (u : User) : IO Reply := do
  let level ← Policy.accountLevel ctx u.id
  return .json (Json.mkObj [("name", u.name),
    ("acr", match level with | some a => Json.str a.identifier | none => Json.null)]) .created

/-- `POST /invite/<token>/finish`: register the credential, creating the
account and consuming the invitation.  User verification is not required:
whether the credential gave it is recorded, and decides the account's level. -/
def finishInvitation : Handler := fun ctx r => do
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let some credJ := (j.getObjVal? "credential").toOption | return badRequest "'credential' is missing"
  let reg ← match parseRegistration credJ with
    | .ok x => pure x
    | .error e => return badRequest e
  let name := credentialName (strField j "name") "passkey"
  limited ctx r .invitationUsed none fun lim attempt => do
    let some h := tokenHashOf r | return noInvitation
    let refuse (why : String) : IO Reply := do
      Audit.log ctx r .invitationUsed .failure (detail := why)
      return Reply.error .badRequest "registration_failed"
        "the authenticator could not be registered"
    let some (challenge, ch) ← consumeRegistrationChallenge ctx reg
      | refuse "unknown or expired challenge"
    -- A challenge issued for an existing account's registration is not one
    -- for an invitation.
    if ch.user.isSome then return ← refuse "challenge issued to an account"
    match ← verifyNewCredential ctx challenge reg (requireUserVerification := false) with
    | .error why => refuse why
    | .ok c =>
      let now ← ctx.clock
      let handle := Secrets.invitationHandle ctx.rootKey challenge
      match ← ctx.store.redeemInvitation h handle
          (.credential fun u => credentialRow c u name reg.transports now) now with
      | .error why =>
        Audit.log ctx r .invitationUsed .failure (detail := why)
        return noInvitation
      | .ok u =>
        lim.succeed attempt
        Audit.log ctx r .invitationUsed .success (userName := some u.name)
        Audit.log ctx r .register .success (userName := some u.name)
          (factor := some ("webauthn:" ++ b64 c.id))
        invitationRedeemed ctx u

/-- `POST /invite/<token>/password`: create the account with a password as its
first way in, where the deployment allows passwords, consuming the
invitation.  The account gets a random WebAuthn user handle, for the passkey
it may add later.  Counted against the rate limiter like the other
invitation endpoints. -/
def finishInvitationPassword : Handler := fun ctx r => do
  if !ctx.config.allowPasswords then
    return Reply.error .forbidden "passwords_disabled" "this deployment does not use passwords"
  let j ← match jsonBody r with
    | .ok j => pure j
    | .error rep => return rep
  let some pw := strField j "password" | return badRequest "'password' is missing"
  if let some rep := passwordProblem pw then return rep
  limited ctx r .invitationUsed none fun lim attempt => do
    let some (h, _) ← invitationOf ctx r | return noInvitation
    let phc ← Factor.Password.hash pw
    let now ← ctx.clock
    match ← ctx.store.redeemInvitation h (← Crypto.randomBytes 32) (.password phc) now with
    | .error why =>
      Audit.log ctx r .invitationUsed .failure (detail := why)
      return noInvitation
    | .ok u =>
      lim.succeed attempt
      Audit.log ctx r .invitationUsed .success (userName := some u.name)
      Audit.log ctx r .register .success (userName := some u.name) (factor := some "password")
      invitationRedeemed ctx u

end SignIn
end Pyle