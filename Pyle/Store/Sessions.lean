import Pyle.Store.Users

/-!
# Sessions and challenges

The rows behind `Pyle.Session` and behind every WebAuthn ceremony.

A session row is keyed by the SHA-256 of its identifier; the identifier itself
lives only in the browser's cookie.  Nothing here inserts a session row or
records an authentication on one: those two statements are private to
`Pyle.Policy`, behind `StrongAuthentication` (DESIGN §9.3).  A challenge is consumed by the first
request that names it, whatever that request's outcome (§2.1), with one
`DELETE … RETURNING`: there is no moment between reading a challenge and
removing it at which a second request could read it too.
-/

namespace Pyle
namespace Store

/-- A session row. -/
structure SessionRow where
  /-- The SHA-256 of the identifier in the cookie. -/
  idHash : SecretHash
  /-- Whose session it is. -/
  user : UserId
  /-- The authentication method references (RFC 8176) of the sign-in. -/
  amr : List String
  /-- The authenticators used: credential ids in base64url, `totp`, `recovery`. -/
  factors : List String
  /-- When the user last authenticated, for `max_age` and step-up (§4). -/
  authTime : Nat
  /-- When the session began; the absolute timeout counts from here. -/
  created : Nat
  /-- When it was last used; the idle timeout counts from here. -/
  lastSeen : Nat
  /-- The client address it was created from, shown in the session list. -/
  clientAddress : String
  /-- The `User-Agent` it was created with, shown in the session list. -/
  userAgent : String

/-- The columns of `sessions`, in the order `readSession` reads them. -/
def sessionColumns : String :=
  "id_hash, user_id, amr, factors, auth_time, created, last_seen, client_address, user_agent"

/-- Read a session row selected with `sessionColumns`. -/
def readSession (stmt : SQLite.Stmt) : IO SessionRow := do
  return {
    idHash := .ofStored (← colBlob stmt 0)
    user := ⟨← colInt stmt 1⟩
    amr := ← colList stmt 2
    factors := ← colList stmt 3
    authTime := ← colNat stmt 4
    created := ← colNat stmt 5
    lastSeen := ← colNat stmt 6
    clientAddress := ← colText stmt 7
    userAgent := ← colText stmt 8 }

/-- Look up the session with this identifier hash that is still live at `now`
— idle for at most `idle` seconds, and at most `absolute` seconds old, and
belonging to an account that is not disabled — and mark it used.  A session
past either timeout is deleted on the way.  The lookup, the expiry and the
touch are one transaction. -/
def Store.touchSession (s : Store) (idHash : SecretHash) (now idle absolute : Nat) :
    IO (Option SessionRow) := s.atomically fun c => do
  let some r ← queryOne c
      s!"SELECT {sessionColumns} FROM sessions WHERE id_hash = ?" #[idHash] readSession
    | return none
  if r.lastSeen + idle < now || r.created + absolute < now then
    discard <| exec c "DELETE FROM sessions WHERE id_hash = ?" #[idHash]
    return none
  let disabled ← queryOne c "SELECT disabled FROM users WHERE id = ?" #[r.user] (colInt · 0)
  if disabled != some 0 then return none
  discard <| exec c "UPDATE sessions SET last_seen = ? WHERE id_hash = ?" #[now, idHash]
  return some { r with lastSeen := now }

/-- Give a session a new identifier, keeping everything else.  Applies only if
the old identifier is still current, so a session can be rotated once from a
given identifier.  Whether it applied. -/
def Store.rotateSession (s : Store) (old new : SecretHash) (now : Nat) : IO Bool :=
  s.run fun c => do
    return (← exec c "UPDATE sessions SET id_hash = ?, last_seen = ? WHERE id_hash = ?"
      #[new, now, old]) > 0

/-- A user's sessions, most recently used first. -/
def Store.listSessions (s : Store) (user : UserId) : IO (Array SessionRow) :=
  s.run fun c => query c
    s!"SELECT {sessionColumns} FROM sessions WHERE user_id = ? ORDER BY last_seen DESC"
    #[user] readSession

/-- End one session.  The user is part of the condition, so one user cannot end
another's session by naming its hash.  Whether it existed. -/
def Store.deleteSession (s : Store) (user : UserId) (idHash : SecretHash) : IO Bool :=
  s.run fun c => do
    return (← exec c "DELETE FROM sessions WHERE id_hash = ? AND user_id = ?"
      #[idHash, user]) > 0

/-- End the session with this identifier hash, whoever's it is.  For a
request's own session, whose identifier the request has just presented.
Whether there was one. -/
def Store.endSession (s : Store) (idHash : SecretHash) : IO Bool := s.run fun c => do
  return (← exec c "DELETE FROM sessions WHERE id_hash = ?" #[idHash]) > 0

/-- End every session of a user; how many there were. -/
def Store.deleteUserSessions (s : Store) (user : UserId) : IO Nat := s.run fun c =>
  exec c "DELETE FROM sessions WHERE user_id = ?" #[user]

/-- Remove every session past either timeout; how many. -/
def Store.purgeSessions (s : Store) (now idle absolute : Nat) : IO Nat := s.run fun c =>
  exec c "DELETE FROM sessions WHERE last_seen + ? < ? OR created + ? < ?"
    #[idle, now, absolute, now]

/-! ## Challenges -/

/-- What a challenge was issued for.  A challenge is only accepted for the
purpose it was issued for. -/
inductive ChallengePurpose where
  /-- Signing in with a WebAuthn assertion. -/
  | authenticate
  /-- Registering a new WebAuthn credential. -/
  | register
  /-- A step-up assertion within an existing session. -/
  | stepUp
  deriving BEq, Repr, Inhabited

/-- The name stored in the `purpose` column. -/
def ChallengePurpose.toString : ChallengePurpose → String
  | .authenticate => "authenticate"
  | .register => "register"
  | .stepUp => "step-up"

instance : ToString ChallengePurpose := ⟨ChallengePurpose.toString⟩

/-- A pending challenge, as it comes back when consumed. -/
structure Challenge where
  /-- The random bytes. -/
  value : ByteArray
  /-- What it was issued for. -/
  purpose : ChallengePurpose
  /-- The user it was issued to, when the ceremony names one. -/
  user : Option UserId
  /-- When it stops being accepted. -/
  expires : Nat

/-- Record a new challenge. -/
def Store.addChallenge (s : Store) (ch : Challenge) : IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO challenges (challenge, purpose, user_id, expires) VALUES (?, ?, ?, ?)"
    #[ch.value, ch.purpose.toString, Value.opt ch.user, ch.expires]

/-- A challenge row as `consumeChallenge` deletes it: the stored purpose, the
user it was issued to, and its expiry. -/
structure ChallengeRow where
  /-- The `purpose` column, as stored. -/
  purpose : String
  /-- The `user_id` column. -/
  user : Option Int
  /-- The `expires` column. -/
  expires : Nat

/-- Whether a deleted challenge row may be used: the challenge `value`, if
the row was there, was issued for `purpose`, and had not expired at `now`.
This is the whole of the decision `consumeChallenge` makes; the store only
deletes the row and hands it here. -/
def challengeDecision (value : ByteArray) (purpose : ChallengePurpose) (now : Nat) :
    Option ChallengeRow → Option Challenge
  | some r =>
    if r.purpose == purpose.toString && now < r.expires then
      some { value, purpose, user := r.user.map (⟨·⟩), expires := r.expires }
    else none
  | none => none

/-- Whether a consumed challenge may be answered by `user`'s credential: a
challenge issued to a user admits only that user, and one issued to no one —
the discoverable flow — admits anyone. -/
def Challenge.admits (ch : Challenge) (user : UserId) : Bool :=
  match ch.user with
  | some u => u == user
  | none => true

/-- Consume a challenge: delete it and return it if it was pending, issued for
`purpose`, and not expired at `now`.  A challenge that exists but fails the
purpose or expiry test is deleted all the same — the first attempt that names
a challenge uses it up, whatever happens next.  The test is
`challengeDecision`. -/
def Store.consumeChallenge (s : Store) (value : ByteArray) (purpose : ChallengePurpose)
    (now : Nat) : IO (Option Challenge) := s.run fun c => do
  let row ← queryOne c
    "DELETE FROM challenges WHERE challenge = ? RETURNING purpose, user_id, expires"
    #[value] fun st => do
      return { purpose := ← colText st 0, user := ← colOpt colInt st 1,
               expires := ← colNat st 2 : ChallengeRow }
  return challengeDecision value purpose now row

/-- Remove every expired challenge; how many. -/
def Store.purgeChallenges (s : Store) (now : Nat) : IO Nat := s.run fun c =>
  exec c "DELETE FROM challenges WHERE expires <= ?" #[now]

end Store
end Pyle