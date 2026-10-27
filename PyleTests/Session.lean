import PyleTests.SignIn

/-!
# Sessions

Creation, lookup through the cookie, both timeouts, rotation, step-up, the
session list, and sign-out through the real route — with the clock moved by
hand.  A session can only be made from a `Policy.Authentication`, so each one
here comes from an assertion of a software passkey (`authFor`).
-/

namespace PyleTests

open Pyle Pyle.Http

/-- Identifiers in the cookie. -/
def idTests : IO Unit := do
  group "session: identifiers"
  let b ← Crypto.randomBytes 32
  let s := Session.encodeId b
  checkEq "43 characters, no padding" s.length 43
  check "no padding" (!s.contains '=')
  check "round-trips" (Session.decodeId s == some b)
  checkEq "too short is refused" (Session.decodeId (s.drop 1).toString) none
  checkEq "padding is refused" (Session.decodeId (s ++ "=")) none
  checkEq "a character outside base64url is refused"
    (Session.decodeId ("+" ++ (s.drop 1).toString)) none

/-- The life of a session. -/
def lifecycleTests : IO Unit := withCtx fun ctx clock => do
  group "session: lifecycle"
  let alice ← ctx.store.addUser "alice" [] 1
  let bob ← ctx.store.addUser "bob" [] 1
  let ak ← SoftKey.new
  enrol ctx alice ak
  let bk ← SoftKey.new
  enrol ctx bob bk
  let start ← clock.get
  let signIn := Req.mk' .post "/" [("User-Agent", "Test/1.0")] (clientAddress := "1.2.3.4")
  let (_, id) ← Policy.establish ctx signIn (← authFor ctx ak)
  let stored ← ctx.store.run fun c =>
    Store.query c "SELECT id_hash FROM sessions" #[] (Store.colBlob · 0)
  check "the database holds the hash of the identifier"
    (stored.size == 1 && (Session.decodeId id).map (Store.SecretHash.of · |>.bytes) ==
      stored[0]?)
  let cur ← Session.current ctx (withCookie id)
  checkEq "the cookie finds the session" (cur.map (·.user)) (some alice.id)
  checkEq "with its amr" (cur.map (·.amr)) (some ["hwk", "user"])
  checkEq "and auth_time" (cur.map (·.authTime)) (some start)
  checkEq "and where it came from" (cur.map fun s => (s.clientAddress, s.userAgent))
    (some ("1.2.3.4", "Test/1.0"))
  checkEq "no cookie, no session" ((← Session.current ctx (Req.mk' .get "/")).isSome) false
  checkEq "an unknown identifier, no session"
    ((← Session.current ctx (withCookie (Session.encodeId (← Crypto.randomBytes 32)))).isSome)
    false
  checkEq "a malformed cookie, no session" ((← Session.current ctx (withCookie "x")).isSome) false
  -- Idle timeout: used within it, the session lives on; left past it, it is gone.
  clock.set (start + ctx.config.sessionIdleSeconds - 1)
  check "used just within the idle timeout" ((← Session.current ctx (withCookie id)).isSome)
  clock.set (start + 2 * ctx.config.sessionIdleSeconds - 2)
  check "the idle timeout counts from the last use"
    ((← Session.current ctx (withCookie id)).isSome)
  clock.set (start + 3 * ctx.config.sessionIdleSeconds)
  check "left idle, it lapses" ((← Session.current ctx (withCookie id)).isNone)
  check "and the row is gone" ((← ctx.store.listSessions alice.id).isEmpty)
  -- Absolute timeout: used throughout, it still ends.
  let t0 ← clock.get
  let (_, id2) ← Policy.establish ctx signIn (← authFor ctx ak)
  let mut t := t0
  let mut alive := true
  while t < t0 + ctx.config.sessionAbsoluteSeconds do
    t := t + ctx.config.sessionIdleSeconds / 2
    clock.set t
    if t ≤ t0 + ctx.config.sessionAbsoluteSeconds then
      alive := alive && (← Session.current ctx (withCookie id2)).isSome
  check "used regularly, it lives until the absolute timeout" alive
  clock.set (t0 + ctx.config.sessionAbsoluteSeconds + 1)
  check "and not past it" ((← Session.current ctx (withCookie id2)).isNone)
  -- Rotation.
  let (s3, id3) ← Policy.establish ctx signIn (← authFor ctx ak)
  let some (_, id3') ← Session.rotate ctx s3
    | check "rotation succeeds" false
  check "the old identifier is dead" ((← Session.current ctx (withCookie id3)).isNone)
  check "the new one works" ((← Session.current ctx (withCookie id3')).isSome)
  check "a session is rotated once from an identifier" ((← Session.rotate ctx s3).isNone)
  -- Step-up.
  let some cur3 ← Session.current ctx (withCookie id3') | check "still there" false
  clock.modify (· + 100)
  let ek ← SoftKey.new .edDsa (backupEligible := true)
  enrol ctx alice ek
  let some (up, id4) ← Policy.stepUp ctx cur3 (← authFor ctx ek)
    | check "step-up succeeds" false
  checkEq "step-up refreshes auth_time" up.authTime (← clock.get)
  check "and rotates" ((← Session.current ctx (withCookie id3')).isNone)
  checkEq "and records the new amr" ((← Session.current ctx (withCookie id4)).map (·.amr))
    (some ["swk", "user"])
  check "it counts as recent" (Session.authenticatedWithin up (← clock.get) 300)
  check "and not after five minutes" (!Session.authenticatedWithin up ((← clock.get) + 301) 300)
  -- The list, and ending sessions.
  discard <| Policy.establish ctx signIn (← authFor ctx ak)
  let (_, bid) ← Policy.establish ctx signIn (← authFor ctx bk)
  let mine ← Session.list ctx alice.id
  checkEq "alice sees her two live sessions" mine.size 2
  let some first := mine[0]? | check "a session to end" false
  check "bob cannot end alice's session" (!(← Session.terminate ctx bob.id first.handle))
  check "alice can" (← Session.terminate ctx alice.id first.handle)
  checkEq "one is left" (← Session.list ctx alice.id).size 1
  checkEq "ending all" (← Session.terminateAll ctx alice.id) 1
  check "bob's is untouched" ((← Session.current ctx (withCookie bid)).isSome)
  discard <| ctx.store.setUserDisabled bob.id true
  check "a disabled account has no session" ((← Session.current ctx (withCookie bid)).isNone)

/-- Signing in replaces the request's session. -/
def replaceTests : IO Unit := withCtx fun ctx _ => do
  group "session: replacement"
  let alice ← ctx.store.addUser "alice" [] 1
  let k ← SoftKey.new
  enrol ctx alice k
  let (_, planted) ← Policy.establish ctx (Req.mk' .post "/") (← authFor ctx k)
  let (_, fresh) ← Policy.establish ctx (withCookie planted .post) (← authFor ctx k)
  check "the session the request carried is ended"
    ((← Session.current ctx (withCookie planted)).isNone)
  check "the new one works" ((← Session.current ctx (withCookie fresh)).isSome)
  checkEq "and it is the only one" (← Session.list ctx alice.id).size 1

/-- Signing out through the route. -/
def logoutTests : IO Unit := withCtx fun ctx _ => do
  group "session: sign-out"
  let alice ← ctx.store.addUser "alice" [] 1
  let k ← SoftKey.new
  enrol ctx alice k
  let (_, id) ← Policy.establish ctx (Req.mk' .post "/") (← authFor ctx k)
  let crossSite ← Server.route ctx (withCookie id .post "/logout"
    [("Origin", "https://evil.example")])
  checkEq "a cross-site sign-out is refused" crossSite.status.toCode 403
  check "and leaves the session" ((← Session.current ctx (withCookie id)).isSome)
  let r ← Server.route ctx (withCookie id .post "/logout" [("Origin", "https://auth.example.org")])
  checkEq "a sign-out answers 204" r.status.toCode 204
  check "and clears the cookie" (hasHeader r "Set-Cookie" clearSessionCookie)
  check "and ends the session" ((← Session.current ctx (withCookie id)).isNone)
  let log ← Audit.entries ctx.store
  checkEq "and is audited" (log.map fun e => (e.event, e.userName, e.outcome))
    #[("sign-out", some "alice", "success")]

/-- Sessions. -/
def sessionTests : IO Unit := do
  idTests
  lifecycleTests
  replaceTests
  logoutTests

end PyleTests