import Std.Data.HashMap
import Std.Net.Addr
import LeanBiscuit.Crypto.Hash

/-!
# Rate limiting

Every endpoint that checks a factor is rate limited per account and per client
address, with exponential back-off (DESIGN.md §7).  The two are counted
separately: one address trying many accounts is stopped by the address count,
and many addresses trying one account by the account count.

The rule is a pure function of a failure count and the time of the last
failure (`Policy.delay`), so it can be read and tested on its own.  After
`freeFailures` failures, each further one doubles the wait, from `baseDelay`
up to `maxDelay`; a key that has seen no failure for `forgetAfter` seconds
starts again from zero.

**Check and record are one step.**  `tryAcquire` checks the wait and, if there
is none, records a failure in the same atomic update (`IO.Ref.modifyGet`), so
a burst of concurrent guesses cannot all pass the check before any of them is
counted.  The failure is provisional: `succeed` takes it back from the address
and clears the account's count — it was the account's owner — but leaves the
address's earlier failures, which would otherwise let an attacker with one
working account reset their own address between guesses.

**Memory is bounded.**  Keys have a fixed size — the first 16 bytes of the
SHA-256 of the normalised account name or address — so a long name costs no
more than a short one.  Entries past `forgetAfter` are swept every
`sweepInterval` seconds, and the table never holds more than `maxEntries`:
when it is full, the oldest quarter is dropped.  Dropping an entry only ever
forgets failures, so under a flood the limiter becomes more lenient, never
stuck.

**Addresses.**  An IPv6 client is keyed by its /64, since one host is usually
given a whole /64 and could otherwise rotate through it.

The state is in memory.  A restart forgets it, which costs an attacker a
restart they cannot cause; and a factor that can be guessed (TOTP) also has a
lock in the database (`Store.recordTotpFailure`) that survives one.
-/

namespace Pyle
namespace Http

/-- How hard to push back. -/
structure Policy where
  /-- Failures allowed before any delay. -/
  freeFailures : Nat := 3
  /-- The first delay, in seconds. -/
  baseDelay : Nat := 1
  /-- The longest delay, in seconds. -/
  maxDelay : Nat := 900
  /-- Seconds without a failure after which a key is forgotten. -/
  forgetAfter : Nat := 3600
  /-- The most keys remembered at once. -/
  maxEntries : Nat := 100000
  /-- Seconds between sweeps of forgotten keys. -/
  sweepInterval : Nat := 300
  deriving Repr, Inhabited

/-- What is remembered about one key. -/
structure Entry where
  /-- Failures since the key was last cleared or forgotten. -/
  failures : Nat
  /-- When the last one was. -/
  lastFailure : Nat
  deriving Repr, Inhabited

/-- The delay a key with `e` must wait after its last failure: zero within the
free failures, then `baseDelay * 2^k`, capped at `maxDelay`. -/
def Policy.delay (p : Policy) (e : Entry) : Nat :=
  if e.failures ≤ p.freeFailures then 0
  else min p.maxDelay (p.baseDelay * 2 ^ (min 32 (e.failures - p.freeFailures - 1)))

/-- How many seconds from `now` a key with entry `e` must still wait, or zero.
A forgotten entry waits for nothing. -/
def Policy.wait (p : Policy) (e : Entry) (now : Nat) : Nat :=
  if e.lastFailure + p.forgetAfter ≤ now then 0
  else (e.lastFailure + p.delay e) - now

/-- A limiter key: 16 bytes of a SHA-256, as two words. -/
structure Key where
  /-- The first eight bytes. -/
  hi : UInt64
  /-- The next eight. -/
  lo : UInt64
  deriving BEq, Hashable, Repr

/-- The key for a tagged name. -/
def Key.ofName (tag name : String) : Key :=
  let d := LeanBiscuit.Sha256.hash (tag ++ ":" ++ name).toUTF8
  let word (off : Nat) : UInt64 :=
    (List.range 8).foldl (fun acc i => (acc <<< 8) ||| (d.get! (off + i)).toUInt64) 0
  { hi := word 0, lo := word 8 }

/-- The part of a client address a limit applies to: an IPv6 address's /64,
anything else as it is. -/
def addressPrefix (address : String) : String :=
  match Std.Net.IPv6Addr.ofString address with
  | some a =>
    let s := a.segments
    s!"{s[0].toNat}:{s[1].toNat}:{s[2].toNat}:{s[3].toNat}::/64"
  | none => address

/-- The key for an account name, normalised: trimmed and lower-cased, so that
`Alice ` and `alice` share a count.  The count exists whether or not the
account does, so the limiter itself does not reveal which ones exist (§7). -/
def Key.account (name : String) : Key := ofName "account" name.trimAscii.toString.toLower

/-- The key for a client address. -/
def Key.client (address : String) : Key := ofName "client" (addressPrefix address)

/-- The keys a request counts against.  The account is optional because some
endpoints check a factor before anyone has said who they are. -/
def keysFor (account : Option String) (client : String) : List Key :=
  (account.map Key.account).toList ++ [Key.client client]

/-- The limiter's state. -/
structure State where
  /-- The entries, by key. -/
  entries : Std.HashMap Key Entry := {}
  /-- When forgotten entries were last swept. -/
  lastSweep : Nat := 0

/-- Drop forgotten entries, if a sweep is due; and if the table is full,
the oldest quarter of what remains. -/
def State.prune (p : Policy) (st : State) (now : Nat) : State := Id.run do
  let mut st := st
  if st.lastSweep + p.sweepInterval ≤ now || st.entries.size ≥ p.maxEntries then
    let live := st.entries.filter fun _ e => e.lastFailure + p.forgetAfter > now
    st := { entries := live, lastSweep := now }
  if st.entries.size ≥ p.maxEntries then
    let byAge := st.entries.toArray.qsort (fun a b => a.2.lastFailure < b.2.lastFailure)
    let drop := max 1 (st.entries.size / 4)
    let kept := (byAge.extract 0 drop).foldl (fun m (k, _) => m.erase k) st.entries
    st := { st with entries := kept }
  return st

/-- Record one failure against `k` at `now`. -/
def State.fail (p : Policy) (st : State) (k : Key) (now : Nat) : State :=
  let failures := match st.entries.get? k with
    | some e => if e.lastFailure + p.forgetAfter ≤ now then 1 else e.failures + 1
    | none => 1
  { st with entries := st.entries.insert k { failures, lastFailure := now } }

/-- The limiter: the policy, and the state.  Every change is one
`IO.Ref.modifyGet`, which is atomic. -/
structure RateLimiter where
  /-- The policy. -/
  policy : Policy
  /-- The state. -/
  state : IO.Ref State

/-- A limiter with no history. -/
def RateLimiter.new (policy : Policy := {}) : IO RateLimiter :=
  return { policy, state := ← IO.mkRef {} }

/-- Permission to make one attempt, with a failure already recorded for it.
Hand it to `RateLimiter.succeed` if the attempt succeeds; drop it otherwise. -/
structure Attempt where
  /-- The account key, if the attempt named one. -/
  account : Option Key
  /-- The client key. -/
  client : Key

/-- Ask to make an attempt.  If any key of the request must still wait, the
longest wait in seconds, and nothing is recorded.  Otherwise a failure is
recorded against every key — in the same atomic step as the check — and the
attempt may go ahead. -/
def RateLimiter.tryAcquire (rl : RateLimiter) (account : Option String) (client : String)
    (now : Nat) : IO (Except Nat Attempt) :=
  rl.state.modifyGet fun st =>
    let p := rl.policy
    let st := st.prune p now
    let keys := keysFor account client
    let wait := keys.foldl (init := 0) fun w k =>
      max w ((st.entries.get? k).elim 0 (p.wait · now))
    if wait > 0 then (.error wait, st)
    else
      let st := keys.foldl (init := st) fun st k => st.fail p k now
      (.ok { account := account.map Key.account, client := Key.client client }, st)

/-- An attempt succeeded: clear the account's count, and take back the
provisional failure from the address, leaving its earlier ones. -/
def RateLimiter.succeed (rl : RateLimiter) (a : Attempt) : IO Unit :=
  rl.state.modify fun st =>
    let entries := match a.account with
      | some k => st.entries.erase k
      | none => st.entries
    let entries := match entries.get? a.client with
      | some e =>
        if e.failures ≤ 1 then entries.erase a.client
        else entries.insert a.client { e with failures := e.failures - 1 }
      | none => entries
    { st with entries }

/-- How many keys the limiter remembers, for tests and monitoring. -/
def RateLimiter.size (rl : RateLimiter) : IO Nat :=
  return (← rl.state.get).entries.size

end Http
end Pyle