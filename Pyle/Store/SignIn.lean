import Pyle.Store.Oidc

/-!
# What sign-in adds to the store

Passwords, for deployments that allow them, and the two invitation
operations the invitation page needs: looking an invitation up without using
it (to greet the person by the name they are invited as), and redeeming it.

**Redeeming is one transaction.**  An invitation is consumed when its first
credential is stored (DESIGN §1): the account and its credential are created
in the same `BEGIN IMMEDIATE` transaction that deletes the invitation, after
checking that the invitation is still live, the name still free and the
credential id not registered to anyone.  Two browsers racing with the same
invitation therefore cannot both create an account, and a registration that
fails part-way leaves the invitation as it was.
-/

namespace Pyle
namespace Store

/-! ## Passwords -/

/-- Store (or replace) a user's password, as the PHC string of its hash. -/
def Store.setPassword (s : Store) (user : UserId) (phc : String) (now : Nat) : IO Unit :=
  s.run fun c => do
    discard <| exec c
      "INSERT INTO passwords (user_id, phc, created) VALUES (?, ?, ?) \
        ON CONFLICT (user_id) DO UPDATE SET phc = excluded.phc, created = excluded.created"
      #[user, phc, now]

/-- A user's password hash, if they have set one. -/
def Store.findPassword (s : Store) (user : UserId) : IO (Option String) := s.run fun c =>
  queryOne c "SELECT phc FROM passwords WHERE user_id = ?" #[user] (colText · 0)

/-- When a user's password was set, if they have one. -/
def Store.passwordSetAt (s : Store) (user : UserId) : IO (Option Nat) := s.run fun c =>
  queryOne c "SELECT created FROM passwords WHERE user_id = ?" #[user] (colNat · 0)

/-- Remove a user's password, unless what is left would not reach a level
(`removeKeepingWayIn`).  A password is not one of the two authenticators §1
counts, so removing it changes that count for nobody, and only the level is
checked.  `passwords` is whether the deployment allows them: if not, the
password is no factor, and removing it takes nothing away. -/
def Store.removePassword (s : Store) (user : UserId) (passwords : Bool := true) :
    IO Removal := s.atomically fun c => do
  let delete := exec c "DELETE FROM passwords WHERE user_id = ?" #[user]
  if passwords then removeKeepingWayIn c user passwords false delete
  else return if (← delete) > 0 then .removed else .notFound

/-! ## Capped challenges -/

/-- Whether a challenge was recorded. -/
inductive ChallengeAdmission where
  /-- It was. -/
  | added
  /-- The client already has as many challenges pending as it may. -/
  | clientFull
  /-- The table already has as many challenges pending as it may. -/
  | full
  deriving BEq, Repr

/-- Record a challenge asked for by `client` (an address, or its /64), unless
that client already has `perClient` challenges pending at `now`, or there are
`total` pending overall.  The counts and the insert are one transaction. -/
def Store.addChallengeCapped (s : Store) (ch : Challenge) (client : String)
    (perClient total now : Nat) : IO ChallengeAdmission := s.atomically fun c => do
  let all ← queryOne c "SELECT COUNT(*) FROM challenges WHERE expires > ?" #[now] (colNat · 0)
  if all.getD 0 ≥ total then return .full
  let mine ← queryOne c
    "SELECT COUNT(*) FROM challenges WHERE client_address = ? AND expires > ?" #[client, now]
    (colNat · 0)
  if mine.getD 0 ≥ perClient then return .clientFull
  discard <| exec c
    "INSERT INTO challenges (challenge, purpose, user_id, expires, client_address, kind) \
      VALUES (?, ?, ?, ?, ?, ?)"
    #[ch.value, ch.purpose.toString, Value.opt ch.user, ch.expires, client, ch.kind]
  return .added

/-- Whether an unspent recovery code with this digest exists, without
spending it. -/
def Store.hasRecoveryCode (s : Store) (user : UserId) (digest : ByteArray) : IO Bool :=
  s.run fun c => do
    return (← queryOne c
      "SELECT 1 FROM recovery_codes WHERE user_id = ? AND digest = ? AND spent_at IS NULL"
      #[user, digest] (colInt · 0)).isSome

/-! ## Invitations -/

/-- Read an invitation row: `user_name, groups, created_by, created, expires`. -/
def readInvitation (st : SQLite.Stmt) : IO Invitation := do
  return { userName := ← colText st 0, groups := ← colList st 1, createdBy := ← colText st 2,
           created := ← colNat st 3, expires := ← colNat st 4 }

/-- The live invitation with this token hash, without using it up. -/
def Store.findInvitation (s : Store) (tokenHash : SecretHash) (now : Nat) :
    IO (Option Invitation) := s.run fun c => do
  let row ← queryOne c
    "SELECT user_name, groups, created_by, created, expires FROM invitations \
      WHERE token_hash = ?" #[tokenHash] readInvitation
  return row.filter (now < ·.expires)

/-- Redeem an invitation by storing its first credential: in one transaction,
check that the invitation is live, its name free and the credential id
unused, then delete the invitation, create the account with the given
WebAuthn user handle, and store the credential `cred` makes for it.  The new
account, or why nothing was done. -/
def Store.redeemInvitation (s : Store) (tokenHash : SecretHash) (handle : ByteArray)
    (cred : UserId → Credential) (now : Nat) : IO (Except String User) :=
  s.atomically fun c => do
    let some inv ← queryOne c
        "SELECT user_name, groups, created_by, created, expires FROM invitations \
          WHERE token_hash = ?" #[tokenHash] readInvitation
      | return .error "no such invitation"
    if inv.expires ≤ now then return .error "the invitation has expired"
    if (← queryOne c "SELECT 1 FROM users WHERE name = ?" #[inv.userName] (colInt · 0)).isSome
    then return .error "the name is taken"
    if (← queryOne c "SELECT 1 FROM users WHERE handle = ?" #[handle] (colInt · 0)).isSome then
      return .error "the user handle is taken"
    let probe := cred ⟨0⟩
    if (← queryOne c "SELECT 1 FROM webauthn_credentials WHERE id = ?" #[probe.id]
        (colInt · 0)).isSome then
      return .error "the credential is already registered"
    discard <| exec c "DELETE FROM invitations WHERE token_hash = ?" #[tokenHash]
    let some u ← queryOne c
        s!"INSERT INTO users (handle, name, groups, created) VALUES (?, ?, ?, ?) \
          RETURNING {userColumns}"
        #[handle, inv.userName, encodeList inv.groups, now] readUser
      | throw (.userError "store: the new user was not returned")
    let k := cred u.id
    discard <| exec c
      "INSERT INTO webauthn_credentials (id, user_id, algorithm, public_key, sign_count, \
        backup_eligible, backup_state, aaguid, transports, name, created, user_verified) \
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
      #[k.id, u.id, k.algorithm, k.publicKey, k.signCount,
        Value.int (if k.backupEligible then 1 else 0),
        Value.int (if k.backupState then 1 else 0), k.aaguid,
        encodeList k.transports, k.name, k.created,
        Value.int (if k.userVerified then 1 else 0)]
    return .ok u

end Store
end Pyle