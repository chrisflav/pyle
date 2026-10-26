import Pyle.Store.Schema
import Pyle.Crypto.Ffi

/-!
# Users and their authenticators

The accounts, and what each one signs in with: WebAuthn credentials, a TOTP
secret and recovery codes (DESIGN.md §1, §3).

The store keeps what the ceremonies need and checks nothing about it: whether
an assertion is good is `Pyle.WebAuthn`'s question, and this module only
remembers the answer.  The one exception is the consume-once operations — a
recovery code is spent, and a TOTP step is used, by a single conditional
`UPDATE`, so two requests racing with the same code cannot both succeed.
-/

namespace Pyle
namespace Store

/-- A row id in `users`. -/
structure UserId where
  /-- The integer key. -/
  val : Int
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : ToString UserId := ⟨fun u => toString u.val⟩
instance : Coe UserId Value := ⟨fun u => .int u.val⟩

/-- An account. -/
structure User where
  /-- The row id. -/
  id : UserId
  /-- The WebAuthn user handle: 32 random bytes, fixed for the account's life. -/
  handle : ByteArray
  /-- The name people and services know the account by. -/
  name : String
  /-- Groups, for services that authorize by them (`Remote-Groups`, §5.3). -/
  groups : List String
  /-- When it was created. -/
  created : Nat
  /-- A disabled account cannot sign in, and its sessions are not honoured. -/
  disabled : Bool

/-- The columns of `users`, in the order `readUser` reads them. -/
def userColumns : String := "id, handle, name, groups, created, disabled"

/-- Read a `users` row selected with `userColumns`. -/
def readUser (stmt : SQLite.Stmt) : IO User := do
  return {
    id := ⟨← colInt stmt 0⟩
    handle := ← colBlob stmt 1
    name := ← colText stmt 2
    groups := ← colList stmt 3
    created := ← colNat stmt 4
    disabled := (← colInt stmt 5) != 0 }

/-- Whether a user name is acceptable: 1 to 64 characters from lower-case
letters, digits, `-`, `_` and `.`, starting with a letter or digit.  Names
appear in tokens, headers and datalog, and a narrow alphabet keeps every one of
those encodings trivial. -/
def validUserName (name : String) : Bool :=
  let cs := name.toList
  !cs.isEmpty && cs.length ≤ 64 &&
    cs.all (fun c => c.isLower || c.isDigit || c == '-' || c == '_' || c == '.') &&
    (cs.head?.any fun c => c.isLower || c.isDigit)

/-- Create an account with a fresh random handle.  Fails if the name is
invalid or taken. -/
def Store.addUser (s : Store) (name : String) (groups : List String) (now : Nat) :
    IO User := do
  unless validUserName name do
    throw (.userError s!"'{name}' is not a valid user name (lower-case letters, digits, \
      '-', '_' and '.', at most 64)")
  let handle ← Crypto.randomBytes 32
  s.atomically fun c => do
    if (← queryOne c "SELECT 1 FROM users WHERE name = ?" #[name] (colInt · 0)).isSome then
      throw (.userError s!"there is already a user named '{name}'")
    let some u ← queryOne c
        s!"INSERT INTO users (handle, name, groups, created) VALUES (?, ?, ?, ?) \
          RETURNING {userColumns}"
        #[handle, name, encodeList groups, now] readUser
      | throw (.userError "store: the new user was not returned")
    return u

/-- Look an account up by name. -/
def Store.findUserByName (s : Store) (name : String) : IO (Option User) := s.run fun c =>
  queryOne c s!"SELECT {userColumns} FROM users WHERE name = ?" #[name] readUser

/-- Look an account up by row id. -/
def Store.findUser (s : Store) (id : UserId) : IO (Option User) := s.run fun c =>
  queryOne c s!"SELECT {userColumns} FROM users WHERE id = ?" #[id] readUser

/-- Look an account up by its WebAuthn user handle. -/
def Store.findUserByHandle (s : Store) (handle : ByteArray) : IO (Option User) :=
  s.run fun c =>
    queryOne c s!"SELECT {userColumns} FROM users WHERE handle = ?" #[handle] readUser

/-- Every account, by name. -/
def Store.listUsers (s : Store) : IO (Array User) := s.run fun c =>
  query c s!"SELECT {userColumns} FROM users ORDER BY name" #[] readUser

/-- Disable or re-enable an account.  Disabling also ends its sessions.
Whether the account existed. -/
def Store.setUserDisabled (s : Store) (id : UserId) (disabled : Bool) : IO Bool :=
  s.atomically fun c => do
    let n ← exec c "UPDATE users SET disabled = ? WHERE id = ?"
      #[(if disabled then (1 : Nat) else 0 : Nat), id]
    if disabled then
      discard <| exec c "DELETE FROM sessions WHERE user_id = ?" #[id]
    return n > 0

/-- Replace an account's groups.  Whether the account existed. -/
def Store.setUserGroups (s : Store) (id : UserId) (groups : List String) : IO Bool :=
  s.run fun c => return (← exec c "UPDATE users SET groups = ? WHERE id = ?"
    #[encodeList groups, id]) > 0

/-! ## WebAuthn credentials -/

/-- A registered WebAuthn credential, as stored.  The public key is kept as
the COSE algorithm number and the key bytes `Pyle.WebAuthn.PublicKey` uses, so
the store does not depend on the WebAuthn modules. -/
structure Credential where
  /-- The credential id the authenticator chose. -/
  id : ByteArray
  /-- Whose it is. -/
  user : UserId
  /-- The COSE algorithm: `-7` for ES256, `-8` for EdDSA. -/
  algorithm : Int
  /-- The public key: 33-byte compressed SEC1 for ES256, 32 bytes for EdDSA. -/
  publicKey : ByteArray
  /-- The last signature counter seen. -/
  signCount : Nat
  /-- The backup-eligible flag at registration, which must never change (§2.1). -/
  backupEligible : Bool
  /-- The backup-state flag last seen. -/
  backupState : Bool
  /-- The authenticator model's AAGUID, 16 bytes (zero when not attested). -/
  aaguid : ByteArray
  /-- The transports the browser reported, as hints for the next ceremony. -/
  transports : List String
  /-- A name the user gave it. -/
  name : String
  /-- When it was registered. -/
  created : Nat
  /-- When it was last used to sign in. -/
  lastUsed : Option Nat
  /-- Whether it has verified the user (a PIN or a fingerprint), at
  registration or in any assertion since: what makes it a passkey rather than
  a security key that is only touched.  Credentials registered before
  migration 5 are assumed to, which is what the invitation that made every
  account's first one required. -/
  userVerified : Bool := true

/-- The columns of `webauthn_credentials`, in the order `readCredential` reads
them. -/
def credentialColumns : String :=
  "id, user_id, algorithm, public_key, sign_count, backup_eligible, backup_state, aaguid, \
    transports, name, created, last_used, user_verified"

/-- Read a credential row selected with `credentialColumns`. -/
def readCredential (stmt : SQLite.Stmt) : IO Credential := do
  return {
    id := ← colBlob stmt 0
    user := ⟨← colInt stmt 1⟩
    algorithm := ← colInt stmt 2
    publicKey := ← colBlob stmt 3
    signCount := ← colNat stmt 4
    backupEligible := (← colInt stmt 5) != 0
    backupState := (← colInt stmt 6) != 0
    aaguid := ← colBlob stmt 7
    transports := ← colList stmt 8
    name := ← colText stmt 9
    created := ← colNat stmt 10
    lastUsed := ← colOpt colNat stmt 11
    userVerified := (← colInt stmt 12) != 0 }

/-- A flag as an integer column. -/
private def flag (b : Bool) : Value := .int (if b then 1 else 0)

/-- Record a newly registered credential.  The id is the primary key, so a
credential id already registered to anyone is refused (§2.2) by the database
itself rather than by a check that could race. -/
def Store.addCredential (s : Store) (cred : Credential) : IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO webauthn_credentials (id, user_id, algorithm, public_key, sign_count, \
      backup_eligible, backup_state, aaguid, transports, name, created, user_verified) \
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    #[cred.id, cred.user, cred.algorithm, cred.publicKey, cred.signCount,
      flag cred.backupEligible, flag cred.backupState, cred.aaguid,
      encodeList cred.transports, cred.name, cred.created, flag cred.userVerified]

/-- Look a credential up by id. -/
def Store.findCredential (s : Store) (id : ByteArray) : IO (Option Credential) :=
  s.run fun c => queryOne c
    s!"SELECT {credentialColumns} FROM webauthn_credentials WHERE id = ?" #[id] readCredential

/-- A user's credentials, oldest first. -/
def Store.listCredentials (s : Store) (user : UserId) : IO (Array Credential) :=
  s.run fun c => query c
    s!"SELECT {credentialColumns} FROM webauthn_credentials WHERE user_id = ? \
      ORDER BY created, id" #[user] readCredential

/-- Record a successful assertion: the new counter, backup state and time,
and that the credential verified the user, if it did this time.
The update only applies if the stored counter is still the one the assertion
was checked against, so two assertions racing with the same counter cannot
both be recorded.  Whether it applied. -/
def Store.recordCredentialUse (s : Store) (id : ByteArray) (expectedCount newCount : Nat)
    (backupState userVerified : Bool) (now : Nat) : IO Bool := s.run fun c => do
  let n ← exec c
    "UPDATE webauthn_credentials SET sign_count = ?, backup_state = ?, last_used = ?, \
      user_verified = MAX(user_verified, ?) WHERE id = ? AND sign_count = ?"
    #[newCount, flag backupState, now, flag userVerified, id, expectedCount]
  return n > 0

/-- Rename a credential.  Whether it belonged to that user. -/
def Store.renameCredential (s : Store) (user : UserId) (id : ByteArray) (name : String) :
    IO Bool := s.run fun c => do
  return (← exec c "UPDATE webauthn_credentials SET name = ? WHERE id = ? AND user_id = ?"
    #[name, id, user]) > 0

/-- How many authenticators a user has: WebAuthn credentials, plus one for a
TOTP secret.  The two-authenticator rule of §1 counts these. -/
def countAuthenticators (c : SQLite) (user : UserId) : IO Nat := do
  let creds ← queryOne c "SELECT COUNT(*) FROM webauthn_credentials WHERE user_id = ?"
    #[user] (colNat · 0)
  let totp ← queryOne c "SELECT COUNT(*) FROM totp WHERE user_id = ?" #[user] (colNat · 0)
  return creds.getD 0 + totp.getD 0

/-- How many authenticators a user has (see `countAuthenticators`). -/
def Store.authenticatorCount (s : Store) (user : UserId) : IO Nat :=
  s.run (countAuthenticators · user)

/-- Run `delete` (which removes one authenticator of `user` and returns how
many rows it removed) only if `user` has more than `keep` authenticators.  The
caller runs this inside `Store.atomically`, so the count and the delete are one
transaction and two concurrent removals cannot both pass the count.  Whether
something was removed. -/
def removeAuthenticatorKeeping (c : SQLite) (user : UserId) (keep : Nat) (delete : IO Nat) :
    IO Bool := do
  if (← countAuthenticators c user) ≤ keep then return false
  return (← delete) > 0

/-- Remove a credential, unless it would leave the user with fewer than
`keep` authenticators (§1: a user cannot remove their second-to-last).
Whether it was removed. -/
def Store.removeCredential (s : Store) (user : UserId) (id : ByteArray) (keep : Nat := 2) :
    IO Bool := s.atomically fun c =>
  removeAuthenticatorKeeping c user keep <|
    exec c "DELETE FROM webauthn_credentials WHERE id = ? AND user_id = ?" #[id, user]

/-! ## TOTP -/

/-- A user's TOTP secret, sealed, with its replay and lockout state. -/
structure TotpRecord where
  /-- Whose it is. -/
  user : UserId
  /-- The secret, sealed under the root key (§6.3).  The store never sees it
  in the clear. -/
  sealedSecret : ByteArray
  /-- The time step of the last code accepted (§3). -/
  lastStep : Option Nat
  /-- Consecutive failed codes. -/
  failures : Nat
  /-- Until when TOTP is locked for this account (§7). -/
  lockedUntil : Nat

/-- Store (or replace) a user's sealed TOTP secret. -/
def Store.setTotp (s : Store) (user : UserId) (sealedSecret : ByteArray) (now : Nat) :
    IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO totp (user_id, secret, created) VALUES (?, ?, ?) \
      ON CONFLICT (user_id) DO UPDATE SET secret = excluded.secret, last_step = NULL, \
      failures = 0, locked_until = 0, created = excluded.created"
    #[user, sealedSecret, now]

/-- A user's TOTP record. -/
def Store.findTotp (s : Store) (user : UserId) : IO (Option TotpRecord) := s.run fun c =>
  queryOne c "SELECT user_id, secret, last_step, failures, locked_until FROM totp \
      WHERE user_id = ?" #[user] fun st => do
    return { user := ⟨← colInt st 0⟩, sealedSecret := ← colBlob st 1,
             lastStep := ← colOpt colNat st 2, failures := ← colNat st 3,
             lockedUntil := ← colNat st 4 }

/-- Remove a user's TOTP secret, under the same rule as `removeCredential`:
not if it would leave fewer than `keep` authenticators.  Whether it was
removed. -/
def Store.removeTotp (s : Store) (user : UserId) (keep : Nat := 2) : IO Bool :=
  s.atomically fun c =>
    removeAuthenticatorKeeping c user keep <|
      exec c "DELETE FROM totp WHERE user_id = ?" #[user]

/-- Record an accepted code for time step `step`.  Applies only if `step` is
strictly later than the last accepted one and TOTP is not locked, in one
conditional `UPDATE`; that is the replay rule of §3 enforced where two
concurrent requests cannot both pass it.  Whether it applied. -/
def Store.acceptTotpStep (s : Store) (user : UserId) (step now : Nat) : IO Bool :=
  s.run fun c => do
    let n ← exec c
      "UPDATE totp SET last_step = ?, failures = 0 \
        WHERE user_id = ? AND (last_step IS NULL OR last_step < ?) AND locked_until <= ?"
      #[step, user, step, now]
    return n > 0

/-- Record a failed code.  After `maxFailures` consecutive failures TOTP is
locked for `lockSeconds` and the count starts again (§7: five, fifteen
minutes).  Returns the time it is locked until, if it now is. -/
def Store.recordTotpFailure (s : Store) (user : UserId) (now : Nat)
    (maxFailures : Nat := 5) (lockSeconds : Nat := 900) : IO (Option Nat) :=
  s.atomically fun c => do
    let some failures ← queryOne c
        "UPDATE totp SET failures = failures + 1 WHERE user_id = ? RETURNING failures"
        #[user] (colNat · 0)
      | return none
    if failures ≥ maxFailures then
      discard <| exec c "UPDATE totp SET failures = 0, locked_until = ? WHERE user_id = ?"
        #[now + lockSeconds, user]
      return some (now + lockSeconds)
    return none

/-! ## Recovery codes -/

/-- Replace a user's recovery codes with new digests (HMAC-SHA256 under a
server key, computed by `Pyle.Factor`). -/
def Store.setRecoveryCodes (s : Store) (user : UserId) (digests : List ByteArray) :
    IO Unit := s.atomically fun c => do
  discard <| exec c "DELETE FROM recovery_codes WHERE user_id = ?" #[user]
  for d in digests do
    discard <| exec c "INSERT INTO recovery_codes (user_id, digest) VALUES (?, ?)" #[user, d]

/-- Spend a recovery code: mark the unspent code with this digest spent, in one
conditional `UPDATE`.  Whether there was one to spend; a code is good once. -/
def Store.spendRecoveryCode (s : Store) (user : UserId) (digest : ByteArray) (now : Nat) :
    IO Bool := s.run fun c => do
  return (← exec c
    "UPDATE recovery_codes SET spent_at = ? \
      WHERE user_id = ? AND digest = ? AND spent_at IS NULL"
    #[now, user, digest]) > 0

/-- How many of a user's recovery codes are unspent. -/
def Store.unspentRecoveryCodes (s : Store) (user : UserId) : IO Nat := s.run fun c => do
  return (← queryOne c
    "SELECT COUNT(*) FROM recovery_codes WHERE user_id = ? AND spent_at IS NULL"
    #[user] (colNat · 0)).getD 0

end Store
end Pyle