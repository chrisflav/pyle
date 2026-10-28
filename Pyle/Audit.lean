import Pyle.Http.Router

/-!
# The audit log

One append-only record per authentication event (DESIGN.md §7), in the shape
of kleis's §9.3: who, which factor, from where, the outcome.  Each record
carries the SHA-256 of the previous record's hash and its own fields, so
changing, removing or reordering any record breaks every hash after it, and
`verifyChain` finds where.

**What the chain does not show.**  It detects a record being modified,
removed from the middle or reordered.  It does not detect someone with write
access to the database cutting off the newest records and appending new ones
in their place: they can recompute every hash from the cut onwards, and the
result is a valid chain.  Only an anchor outside the database closes that:
periodically exporting the head hash (the last entry's `hash`) somewhere the
database's writer cannot rewrite, and checking that the chain still passes
through it.

**Never a secret.**  A record has no field for one: the event is a fixed name,
the factor is a kind of authenticator or a credential id, the user is a name.
`detail` is free text for a reason ("unknown credential", "counter went
backwards"); callers put reasons there, never a code, a challenge or a token,
and nothing in pyle passes a secret to `append`.

**Bounded and sanitised.**  What a client typed reaches the log — a failed
sign-in records the name that was tried — so `append` cleans every field
first (`sanitise`).  A user name that is not a valid one is never logged
verbatim: it becomes `invalidUserName`, since it may be a password typed into
the wrong box.  Other fields lose control characters and are cut to a fixed
length, so a request cannot make a record unbounded or break a terminal that
displays it.

**The hash.**  `SHA-256(prev ‖ field₁ ‖ … ‖ fieldₙ)`, where every field is
written with an explicit length (or a presence tag for an optional one) so
that no two different records encode to the same bytes.  The first record's
`prev` is 32 zero bytes.
-/

namespace Pyle
namespace Audit

open Store

/-- What happened. -/
inductive Event where
  /-- A sign-in attempt. -/
  | signIn
  /-- A step-up within a session. -/
  | stepUp
  /-- A sign-out, or a session ended from the session list. -/
  | signOut
  /-- An authenticator registered. -/
  | register
  /-- An authenticator removed. -/
  | removeAuthenticator
  /-- A recovery code used. -/
  | recoveryCode
  /-- TOTP locked after repeated failures. -/
  | totpLocked
  /-- An authenticator app's stored secret did not open under the root key,
  and the app was left out of a code check. -/
  | totpSecretUnreadable
  /-- An account created. -/
  | userAdded
  /-- An account disabled or re-enabled. -/
  | userChanged
  /-- Tokens issued to a client. -/
  | tokenIssued
  /-- A used refresh token presented again, revoking its family. -/
  | refreshReuse
  /-- A device authorization approved or denied. -/
  | deviceDecision
  /-- An invitation redeemed. -/
  | invitationUsed
  /-- An account removed, with everything that was its. -/
  | userRemoved
  /-- Sessions and refresh-token families ended by an administrator, an
  account's or everyone's. -/
  | sessionsRevoked
  /-- The root key replaced and everything sealed under it re-sealed. -/
  | rootKeyRotated
  deriving BEq, Repr, Inhabited

/-- The name stored for an event. -/
def Event.toString : Event → String
  | .signIn => "sign-in"
  | .stepUp => "step-up"
  | .signOut => "sign-out"
  | .register => "register"
  | .removeAuthenticator => "remove-authenticator"
  | .recoveryCode => "recovery-code"
  | .totpLocked => "totp-locked"
  | .totpSecretUnreadable => "totp-secret-unreadable"
  | .userAdded => "user-added"
  | .userChanged => "user-changed"
  | .tokenIssued => "token-issued"
  | .refreshReuse => "refresh-reuse"
  | .deviceDecision => "device-decision"
  | .invitationUsed => "invitation-used"
  | .userRemoved => "user-removed"
  | .sessionsRevoked => "sessions-revoked"
  | .rootKeyRotated => "root-key-rotated"

instance : ToString Event := ⟨Event.toString⟩

/-- How it ended. -/
inductive Outcome where
  /-- It succeeded. -/
  | success
  /-- A factor was wrong or a check failed. -/
  | failure
  /-- It was not attempted: rate limited, locked, or not allowed. -/
  | refused
  deriving BEq, Repr, Inhabited

/-- The name stored for an outcome. -/
def Outcome.toString : Outcome → String
  | .success => "success"
  | .failure => "failure"
  | .refused => "refused"

instance : ToString Outcome := ⟨Outcome.toString⟩

/-- A record to append. -/
structure Record where
  /-- What happened. -/
  event : Event
  /-- The account it concerns, by name, when there is one.  For a failed
  sign-in this is the name that was tried, which may not exist. -/
  userName : Option String := none
  /-- The factor: `webauthn:<credential id>`, `totp`, `recovery`, `password`. -/
  factor : Option String := none
  /-- Where the request came from, or `cli` for an administration command. -/
  clientAddress : String
  /-- How it ended. -/
  outcome : Outcome
  /-- Why, in a few words.  Never a secret. -/
  detail : String := ""

/-- A record as stored, with its place in the chain.  The event and outcome
are kept as the stored strings, so that a log written by a newer pyle with
events this one does not know still verifies. -/
structure Entry where
  /-- Its position, from 1. -/
  seq : Nat
  /-- When, in seconds since the Unix epoch. -/
  time : Nat
  /-- The event's name. -/
  event : String
  /-- The account's name. -/
  userName : Option String
  /-- The factor. -/
  factor : Option String
  /-- The client address. -/
  clientAddress : String
  /-- The outcome's name. -/
  outcome : String
  /-- The reason. -/
  detail : String
  /-- The previous entry's hash, or 32 zero bytes for the first. -/
  prev : ByteArray
  /-- This entry's hash. -/
  hash : ByteArray

/-- The `prev` of the first entry. -/
def genesis : ByteArray := ⟨Array.replicate 32 0⟩

/-- A number as 8 bytes, big-endian. -/
def encodeNat (n : Nat) : ByteArray :=
  ⟨(List.range 8).reverse.toArray.map fun i => UInt8.ofNat (n >>> (8 * i))⟩

/-- A string with its length in front. -/
def encodeStr (s : String) : ByteArray :=
  let b := s.toUTF8
  encodeNat b.size ++ b

/-- An optional string: a tag byte, then the string if present. -/
def encodeOpt : Option String → ByteArray
  | none => ⟨#[0]⟩
  | some s => ⟨#[1]⟩ ++ encodeStr s

/-- The hash an entry should have, from its `prev` and fields. -/
def Entry.computeHash (e : Entry) : ByteArray :=
  LeanBiscuit.Sha256.hash <|
    e.prev ++ encodeNat e.seq ++ encodeNat e.time ++ encodeStr e.event ++
    encodeOpt e.userName ++ encodeOpt e.factor ++ encodeStr e.clientAddress ++
    encodeStr e.outcome ++ encodeStr e.detail

/-- Check a chain from its first entry: positions count up from 1, each `prev`
is the previous hash, and each hash is right.  The number of entries, or the
first one that is wrong and how. -/
def verifyChain (entries : List Entry) : Except String Nat :=
  go entries 1 genesis
where
  /-- Check from position `seq`, expecting `prev`. -/
  go : List Entry → Nat → ByteArray → Except String Nat
    | [], seq, _ => .ok (seq - 1)
    | e :: rest, seq, prev => do
      unless e.seq == seq do throw s!"entry {e.seq}: expected entry {seq} here"
      unless e.prev == prev do throw s!"entry {e.seq}: does not follow from entry {seq - 1}"
      unless e.computeHash == e.hash do throw s!"entry {e.seq}: its hash does not match"
      go rest (seq + 1) e.hash

/-- The columns of `audit`, in the order `readEntry` reads them. -/
def entryColumns : String :=
  "seq, time, event, user_name, factor, client_address, outcome, detail, prev, hash"

/-- Read an audit row selected with `entryColumns`. -/
def readEntry (st : SQLite.Stmt) : IO Entry := do
  return {
    seq := ← colNat st 0, time := ← colNat st 1, event := ← colText st 2,
    userName := ← colOpt colText st 3, factor := ← colOpt colText st 4,
    clientAddress := ← colText st 5, outcome := ← colText st 6, detail := ← colText st 7,
    prev := ← colBlob st 8, hash := ← colBlob st 9 }

/-- What is logged in place of a user name that is not a valid one. -/
def invalidUserName : String := "<invalid user name>"

/-- A field without control characters, at most `max` characters long. -/
def clean (max : Nat) (s : String) : String :=
  (String.ofList (s.toList.filter fun c => c.toNat ≥ 0x20 && c.toNat != 0x7f)).take max
    |>.toString

/-- The longest `detail` kept: room for an email-address change, old and new
address at their longest (`"email: <254> -> <254>"`). -/
def maxDetailLength : Nat := 640

/-- A record as it is logged: the user name kept only if it is a valid one,
every other field cleaned and bounded. -/
def sanitise (r : Record) : Record :=
  { r with
    userName := r.userName.map fun n => if validUserName n then n else invalidUserName
    factor := r.factor.map (clean 128)
    clientAddress := clean 64 r.clientAddress
    detail := clean maxDetailLength r.detail }

/-- Append a record at time `now`, after `sanitise`, on a connection that is
already inside a transaction — for an administrative change that is to be
recorded in the transaction that makes it.  `append` is this in a
transaction of its own. -/
def appendIn (c : SQLite) (now : Nat) (r : Record) : IO Entry := do
  let r := sanitise r
  let last ← queryOne c "SELECT seq, hash FROM audit ORDER BY seq DESC LIMIT 1" #[]
    fun st => return (← colNat st 0, ← colBlob st 1)
  let (seq, prev) := match last with
    | some (n, h) => (n + 1, h)
    | none => (1, genesis)
  let e : Entry :=
    { seq, time := now, event := r.event.toString, userName := r.userName,
      factor := r.factor, clientAddress := r.clientAddress, outcome := r.outcome.toString,
      detail := r.detail, prev, hash := .empty }
  let e := { e with hash := e.computeHash }
  discard <| exec c
    s!"INSERT INTO audit ({entryColumns}) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    #[e.seq, e.time, e.event, Value.opt e.userName, Value.opt e.factor, e.clientAddress,
      e.outcome, e.detail, e.prev, e.hash]
  return e

/-- Append a record at time `now`, after `sanitise`.  Reading the last hash and inserting the
next entry are one transaction, so concurrent appends cannot fork the chain. -/
def append (s : Store) (now : Nat) (r : Record) : IO Entry := s.atomically (appendIn · now r)

/-- Append a record about a request, at the context's time, from the
request's client address. -/
def log (ctx : Http.Ctx) (req : Http.Req) (event : Event) (outcome : Outcome)
    (userName : Option String := none) (factor : Option String := none)
    (detail : String := "") : IO Unit := do
  discard <| append ctx.store (← ctx.clock)
    { event, outcome, userName, factor, clientAddress := req.clientAddress, detail }

/-- Every entry, in order. -/
def entries (s : Store) : IO (Array Entry) := s.run fun c =>
  query c s!"SELECT {entryColumns} FROM audit ORDER BY seq" #[] readEntry

/-- Verify the whole stored chain. -/
def verify (s : Store) : IO (Except String Nat) :=
  return verifyChain (← entries s).toList

/-! ## Email addresses and display names

Services key accounts by their email address, so which account had which
address, and when, is a question the log must answer: changes record the
addresses themselves.  An address is printable ASCII without spaces
(`normalizeEmail`), so `->` and `;` cannot be mistaken inside one; a display
name has no control characters (`normalizeDisplayName`) and is quoted. -/

/-- An optional address as the log writes it. -/
def showEmail : Option String → String
  | some e => e
  | none => "none"

/-- An optional display name as the log writes it. -/
def showDisplayName : Option String → String
  | some n => s!"\"{n}\""
  | none => "none"

/-- The details of a change to an account's address and display name, one per
field that changed: `email: a@x -> b@y`, `email: a@x -> none`,
`display name: "Ann" -> none`. -/
def contactChanges (before after : User) : List String :=
  (if before.email != after.email then
    [s!"email: {showEmail before.email} -> {showEmail after.email}"] else []) ++
  (if before.displayName != after.displayName then
    [s!"display name: {showDisplayName before.displayName} -> \
      {showDisplayName after.displayName}"] else [])

/-- The details of a new account's or an invitation's address and display
name, those it has, joined with `; `. -/
def contactDetail (email displayName : Option String) : String :=
  "; ".intercalate <|
    (email.map (s!"email: {·}")).toList ++
    (displayName.map fun n => s!"display name: {showDisplayName (some n)}").toList

end Audit
end Pyle