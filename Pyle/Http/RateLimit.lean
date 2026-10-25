import Std.Data.HashMap

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
starts again from zero.  A success clears the account's count — it was the
account's owner — but not the address's, which would otherwise let an
attacker with one working account reset their own address between guesses.

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

/-- What a limiter keys on: an account, or a client address. -/
inductive Key where
  /-- An account name, as typed: the count exists whether or not the account
  does, so the limiter itself does not reveal which ones exist (§7). -/
  | account (name : String)
  /-- A client address. -/
  | client (address : String)
  deriving BEq, Hashable, Repr

/-- The limiter: the policy, and the entries.  `IO.Ref.modify` is atomic, so
concurrent handlers recording failures do not lose each other's counts. -/
structure RateLimiter where
  /-- The policy. -/
  policy : Policy
  /-- The entries, by key. -/
  entries : IO.Ref (Std.HashMap Key Entry)

/-- A limiter with no history. -/
def RateLimiter.new (policy : Policy := {}) : IO RateLimiter :=
  return { policy, entries := ← IO.mkRef {} }

/-- The keys a request counts against.  The account is optional because some
endpoints check a factor before anyone has said who they are. -/
def keysFor (account : Option String) (client : String) : List Key :=
  (account.map Key.account).toList ++ [Key.client client]

/-- How many seconds a request must still wait before trying, or zero if it
may go ahead.  The longest wait of its keys. -/
def RateLimiter.retryAfter (rl : RateLimiter) (account : Option String) (client : String)
    (now : Nat) : IO Nat := do
  let m ← rl.entries.get
  return (keysFor account client).foldl (init := 0) fun w k =>
    max w ((m.get? k).elim 0 (rl.policy.wait · now))

/-- Record a failure against every key of the request. -/
def RateLimiter.recordFailure (rl : RateLimiter) (account : Option String) (client : String)
    (now : Nat) : IO Unit :=
  rl.entries.modify fun m =>
    -- Forget stale keys now and then, so the table does not grow without bound.
    let m := if m.size < 10000 then m else
      m.filter fun _ e => e.lastFailure + rl.policy.forgetAfter > now
    (keysFor account client).foldl (init := m) fun m k =>
      let failures := match m.get? k with
        | some e => if e.lastFailure + rl.policy.forgetAfter ≤ now then 1 else e.failures + 1
        | none => 1
      m.insert k { failures, lastFailure := now }

/-- Record a success: clear the account's count, and leave the address's. -/
def RateLimiter.recordSuccess (rl : RateLimiter) (account : Option String) : IO Unit :=
  match account with
  | some a => rl.entries.modify (·.erase (.account a))
  | none => pure ()

end Http
end Pyle