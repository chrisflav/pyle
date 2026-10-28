import Pyle.SignIn.Common

/-!
# Invitations

Accounts are created by an administrator or by invitation, never by sign-up
(DESIGN, non-goals).  `pyle invite <name>` stores an invitation under the
SHA-256 of a random token and prints `<issuer>/invite/<token>`; whoever opens
that link registers the account's first passkey there.

| | body | answer |
| --- | --- | --- |
| `POST /invite/<token>/begin` | `{}` | creation options |
| `POST /invite/<token>/finish` | `{"credential", "name"?}` | `201 {"name"}` |

The account does not exist until its first credential is stored, and the
invitation is consumed in the same transaction (`Store.redeemInvitation`), so
an invitation creates at most one account and a registration that fails
leaves it usable.  The credential must be discoverable and verify the user —
a passkey — since it is the account's only way in until a second is added;
the page then sends the person on to `/signin` to sign in with it, so that
the session comes from an assertion like every other (`Policy`).

The account's WebAuthn user handle has to be in the creation options, before
the account exists.  `begin` draws 32 random bytes for it and records them
with the registration challenge (`Challenge.userHandle`, migration 9), and
`finish` creates the account with the handle its challenge carries.  A
challenge begun before migration 9 carries none; its handle was derived from
the challenge under a key of its own (`Secrets.invitationHandle`) and is
derived again.  Recording it means a root-key rotation between `begin` and
`finish` cannot give the account a handle other than the one its passkey
holds.
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

/-- The longest an invitation may live: ninety days.  A link is a way into an
account nobody has yet, and the bound also keeps its expiry a time the
database can hold. -/
def maxInvitationSeconds : Nat := 90 * 86400

/-- Issue an invitation for a new account, valid for `ttl` seconds, at most
`maxInvitationSeconds`; the URL to hand to the person.  The account it
creates gets `email` and `displayName`, if given (`normalizeEmail`,
`normalizeDisplayName`).  Fails if the lifetime is too long, the name is
invalid or already taken, or the address invalid or already another
account's; an address taken between now and the redemption makes the
redemption fail.  Only the token's hash is stored. -/
def createInvitation (store : Store) (issuer name : String) (groups : List String)
    (ttl now : Nat) (createdBy : String := "cli") (email displayName : Option String := none) :
    IO String := do
  if ttl > maxInvitationSeconds then
    throw (.userError s!"an invitation lives at most {maxInvitationSeconds / 86400} days")
  unless validUserName name do
    throw (.userError s!"'{name}' is not a valid user name (lower-case letters, digits, \
      '-', '_' and '.', at most 64)")
  let (email, displayName) ← normalizeContact email displayName
  if (← store.findUserByName name).isSome then
    throw (.userError s!"there is already a user named '{name}'")
  if let some e := email then
    if let some owner ← store.run (emailOwner · e) then throw (emailTaken e owner)
  let token ← Crypto.randomBytes invitationTokenBytes.toUSize
  store.addInvitation (.of token)
    { userName := name, groups, createdBy, created := now, expires := now + ttl, email,
      displayName }
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
first passkey.  Counted against the rate limiter, since it tests a token. -/
def beginInvitation : Handler := fun ctx r =>
  limited ctx r .invitationUsed none fun lim attempt => do
    let some (_, inv) ← invitationOf ctx r | return noInvitation
    lim.succeed attempt
    let handle ← Crypto.randomBytes 32
    let ch ← match ← newChallenge ctx r .register none (userHandle := some handle) with
      | .ok ch => pure ch
      | .error rep => return rep
    return .json (creationOptions ctx ch handle inv.userName [] "required" "required")

/-- `POST /invite/<token>/finish`: register the passkey, creating the account
and consuming the invitation. -/
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
      return Reply.error .badRequest "registration_failed" "the passkey could not be registered"
    let some (challenge, ch) ← consumeRegistrationChallenge ctx reg
      | refuse "unknown or expired challenge"
    -- A challenge issued for an existing account's registration is not one
    -- for an invitation.
    if ch.user.isSome then return ← refuse "challenge issued to an account"
    match ← verifyNewCredential ctx challenge reg (requireUserVerification := true) with
    | .error why => refuse why
    | .ok c =>
      let now ← ctx.clock
      let handle := ch.userHandle.getD (Secrets.invitationHandle ctx.rootKey challenge)
      match ← ctx.store.redeemInvitation h handle
          (fun u => credentialRow c u name reg.transports now) now with
      | .error why =>
        Audit.log ctx r .invitationUsed .failure (detail := why)
        return noInvitation
      | .ok u =>
        lim.succeed attempt
        Audit.log ctx r .invitationUsed .success (userName := some u.name)
        Audit.log ctx r .register .success (userName := some u.name)
          (factor := some ("webauthn:" ++ b64 c.id))
        return .json (Json.mkObj [("name", u.name)]) .created

end SignIn
end Pyle