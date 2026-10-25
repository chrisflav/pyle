import PyleTests.Store

/-!
# HTTP

The pieces every request passes through — cookies, bodies, the `Origin`
check, the security headers, client addresses, the rate limiter, the router —
driven as functions, and one request over a real socket to the real server.
-/

namespace PyleTests

open Pyle Pyle.Http
open Std.Http (Method)

/-- Cookie parsing and the session cookie's attributes. -/
def cookieTests : IO Unit := do
  group "http: cookies"
  checkEq "pairs are split and trimmed" (parseCookies "a=1; b = 2 ;c=x=y")
    [("a", "1"), ("b", "2"), ("c", "x=y")]
  checkEq "malformed pairs are skipped" (parseCookies "junk; =v; a=1") [("a", "1")]
  let r := Req.mk' .get "/" [("Cookie", "x=1; __Host-pyle=abc"), ("Cookie", "__Host-pyle=def")]
  checkEq "the first value of a name wins" (r.cookie sessionCookieName) (some "abc")
  checkEq "absent is none" ((Req.mk' .get "/").cookie sessionCookieName) none
  let c := sessionCookie "v" 60
  check "the cookie is __Host-" (c.startsWith "__Host-pyle=v;")
  for attr in ["Path=/", "Secure", "HttpOnly", "SameSite=Lax", "Max-Age=60"] do
    check s!"the cookie has {attr}" ((c.splitOn "; ").contains attr)
  check "the cookie has no Domain" (!(c.splitOn "; ").any (·.startsWith "Domain"))
  check "clearing sets Max-Age=0" ((clearSessionCookie.splitOn "; ").contains "Max-Age=0")

/-- Percent-decoding, forms and JSON bodies. -/
def bodyTests : IO Unit := do
  group "http: bodies"
  checkEq "percent escapes decode" (percentDecode "a%20b%2Bc+d") (some "a b+c d")
  checkEq "UTF-8 escapes decode" (percentDecode "%C3%A9") (some "é")
  checkEq "a truncated escape fails" (percentDecode "a%2") none
  checkEq "a bad hex digit fails" (percentDecode "%zz") none
  checkEq "an escape that is not UTF-8 fails" (percentDecode "%FF") none
  checkEq "an escaped NUL fails" (percentDecode "alice%00x") none
  checkEq "plus is a plus outside forms" (percentDecode "a+b" (plusIsSpace := false)) (some "a+b")
  checkEq "forms parse" (parseUrlEncoded "a=1&b=&c&&d=x%3Dy")
    (some [("a", "1"), ("b", ""), ("c", ""), ("d", "x=y")])
  checkEq "an empty form is empty" (parseUrlEncoded "") (some [])
  checkEq "a malformed form fails" (parseUrlEncoded "a=%") none
  checkEq "a parameter given once is found" (lookupOnce [("a", "1"), ("b", "2")] "a") (some "1")
  checkEq "a parameter given twice is absent" (lookupOnce [("a", "1"), ("a", "2")] "a") none
  let form := Req.mk' .post "/x" [("Content-Type", "application/x-www-form-urlencoded")]
    "code=abc&state=xyz".toUTF8
  checkEq "a form body is read" ((form.form.toOption).bind (lookupOnce · "state")) (some "xyz")
  let notForm := Req.mk' .post "/x" [("Content-Type", "text/plain")] "code=abc".toUTF8
  check "a form body needs the form type" (notForm.form.toOption.isNone)
  let json := Req.mk' .post "/x" [("Content-Type", "application/json; charset=utf-8")]
    "{\"a\": 1}".toUTF8
  check "a JSON body is read" ((json.json.toOption.bind (·.getObjValAs? Nat "a" |>.toOption)) ==
    some 1)
  let badJson := Req.mk' .post "/x" [("Content-Type", "application/json")] "{".toUTF8
  check "malformed JSON is refused" badJson.json.toOption.isNone
  let nul := Req.mk' .post "/x" [("Content-Type", "application/json")]
    "{\"name\": \"alice\\u0000x\"}".toUTF8
  check "JSON with NUL in a string is refused" nul.json.toOption.isNone
  let nulKey := Req.mk' .post "/x" [("Content-Type", "application/json")]
    "{\"a\": [{\"x\\u0000\": 1}]}".toUTF8
  check "and in a nested key" nulKey.json.toOption.isNone
  let notUtf8 := Req.mk' .post "/x" [("Content-Type", "application/json")] ⟨#[0xff, 0xfe]⟩
  check "a body that is not UTF-8 is refused" notUtf8.json.toOption.isNone
  checkEq "query strings parse" ((Req.mk' .get "/a?x=1&y=%20").queryParams.toOption)
    (some [("x", "1"), ("y", " ")])

/-- Paths, client addresses and the `Origin` check as functions. -/
def securityTests : IO Unit := do
  group "http: paths, addresses and origins"
  checkEq "segments" (pathSegments "/a/b/") (some ["a", "b"])
  checkEq "a relative path is refused" (pathSegments "a/b") none
  checkEq "dot-dot is refused" (pathSegments "/a/../b") none
  checkEq "an escaped dot-dot is refused" (pathSegments "/a/%2E%2e/b") none
  checkEq "patterns match with parameters"
    (matchPattern (parsePattern "/sessions/:id") ["sessions", "abc"]) (some [("id", "abc")])
  checkEq "patterns need every segment" (matchPattern (parsePattern "/a/:id") ["a"]) none
  checkEq "an untrusted peer is the client" (clientAddress [] "10.0.0.1" (some "1.2.3.4"))
    "10.0.0.1"
  checkEq "a trusted proxy's last hop is the client"
    (clientAddress ["127.0.0.1"] "127.0.0.1" (some "6.6.6.6, 1.2.3.4")) "1.2.3.4"
  checkEq "trusted hops are skipped from the right"
    (clientAddress ["127.0.0.1", "10.0.0.2"] "127.0.0.1" (some "1.2.3.4, 10.0.0.2"))
    "1.2.3.4"
  checkEq "repeated X-Forwarded-For fields are joined in order"
    (forwardedFor [("x-forwarded-for", "6.6.6.6"), ("x-forwarded-for", "1.2.3.4, 5.5.5.5")])
    (some "6.6.6.6, 1.2.3.4, 5.5.5.5")
  checkEq "so a client's own field cannot hide the proxy's"
    (clientAddress ["127.0.0.1"] "127.0.0.1"
      (forwardedFor [("x-forwarded-for", "6.6.6.6"), ("x-forwarded-for", "1.2.3.4")]))
    "1.2.3.4"
  checkEq "a trusted proxy without the header is the client"
    (clientAddress ["127.0.0.1"] "127.0.0.1" none) "127.0.0.1"
  checkEq "the port is not part of an IPv4 address" (stripPort "1.2.3.4:567") "1.2.3.4"
  let origins := ["https://auth.example.org"]
  check "a configured origin is allowed"
    (originAllowed origins (Req.mk' .post "/" [("Origin", "https://auth.example.org")]))
  check "another origin is not"
    (!originAllowed origins (Req.mk' .post "/" [("Origin", "https://evil.example")]))
  check "a missing origin is not" (!originAllowed origins (Req.mk' .post "/"))
  check "the null origin is not" (!originAllowed origins (Req.mk' .post "/" [("Origin", "null")]))
  check "a prefix is not"
    (!originAllowed origins (Req.mk' .post "/" [("Origin", "https://auth.example.org.evil")]))

/-- The rate limiter's arithmetic and bookkeeping. -/
def rateLimitTests : IO Unit := do
  group "http: rate limiting"
  let p : Policy := { freeFailures := 3, baseDelay := 1, maxDelay := 60, forgetAfter := 600 }
  checkEq "free failures cost nothing" ((List.range 4).map fun n => p.delay ⟨n, 0⟩) [0, 0, 0, 0]
  checkEq "then the delay doubles" ((List.range 4).map fun n => p.delay ⟨n + 4, 0⟩) [1, 2, 4, 8]
  checkEq "up to the cap" (p.delay ⟨100, 0⟩) 60
  checkEq "a forgotten key waits for nothing" (p.wait ⟨100, 0⟩ 600) 0
  let rl ← RateLimiter.new p
  let acquire (a : Option String) (c : String) (now : Nat) : IO (Option Nat) := do
    match ← rl.tryAcquire a c now with
    | .ok _ => return none
    | .error w => return some w
  for _ in [0:5] do discard <| acquire (some "alice") "1.2.3.4" 1000
  -- Five attempts: four went ahead (three free, the fourth after a zero wait),
  -- the fifth was refused and not counted.
  checkEq "after four failures: one second" (← acquire (some "alice") "1.2.3.4" 1000) (some 1)
  checkEq "the account is limited from elsewhere" (← acquire (some "alice") "9.9.9.9" 1000)
    (some 1)
  checkEq "the address is limited for other accounts" (← acquire (some "bob") "1.2.3.4" 1000)
    (some 1)
  checkEq "names are normalised" (← acquire (some " Alice") "9.9.9.9" 1000) (some 1)
  checkEq "others are not" (← acquire (some "carol") "8.8.8.8" 1000) none
  let rl2 ← RateLimiter.new p
  let mut last : Option Attempt := none
  for _ in [0:3] do
    if let .ok a ← rl2.tryAcquire (some "dave") "5.5.5.5" 1000 then last := some a
  if let some a := last then rl2.succeed a
  checkEq "a success clears the account"
    ((← rl2.tryAcquire (some "dave") "6.6.6.6" 1000) matches .ok _) true
  checkEq "and takes back only its own failure from the address"
    ((← rl2.state.get).entries.get? (Key.client "5.5.5.5") |>.map (·.failures)) (some 2)
  -- A success is not a failure: with four failures on an address, a success
  -- a minute later leaves the next attempt free to go ahead at once.
  let rl7 ← RateLimiter.new p
  for _ in [0:4] do discard <| rl7.tryAcquire none "4.4.4.4" 1000
  if let .ok a ← rl7.tryAcquire (some "frank") "4.4.4.4" 1060 then rl7.succeed a
  checkEq "a success leaves the address's last failure where it was"
    ((← rl7.state.get).entries.get? (Key.client "4.4.4.4") |>.map
      fun e => (e.failures, e.lastFailure)) (some (4, 1000))
  checkEq "so it does not restart the delay"
    ((← rl7.tryAcquire (some "frank") "4.4.4.4" 1060) matches .ok _) true
  -- Check and record are one step: a burst gets exactly the free attempts.
  let rl3 ← RateLimiter.new p
  checkEq "sixteen concurrent attempts: four go ahead"
    (← raceCount 16 do return (← rl3.tryAcquire (some "eve") "7.7.7.7" 1000) matches .ok _) 4
  -- IPv6 addresses share a count per /64.
  let rl4 ← RateLimiter.new p
  for i in [0:4] do discard <| rl4.tryAcquire none s!"2001:db8:1:2::{i + 1}" 1000
  checkEq "one /64 shares a count" (← rl4.tryAcquire none "2001:db8:1:2:ffff::9" 1000 |>.map
    (· matches .error _)) true
  checkEq "another /64 does not" (← rl4.tryAcquire none "2001:db8:1:3::1" 1000 |>.map
    (· matches .ok _)) true
  -- Memory is bounded, whatever the keys.
  let small : Policy := { p with maxEntries := 64, sweepInterval := 1000000 }
  let rl5 ← RateLimiter.new small
  for i in [0:500] do
    discard <| rl5.tryAcquire (some (String.ofList (List.replicate 1000 'x') ++ toString i))
      s!"10.0.{i / 256}.{i % 256}" (1000 + i)
  check "the table never exceeds its cap" ((← rl5.size) ≤ 64) s!"{← rl5.size}"
  let rl6 ← RateLimiter.new { p with sweepInterval := 10 }
  for i in [0:20] do discard <| rl6.tryAcquire none s!"10.1.0.{i}" 1000
  discard <| rl6.tryAcquire none "10.2.0.1" 5000
  checkEq "forgotten entries are swept" (← rl6.size) 1

/-- Whether `sub` occurs in `s`. -/
def containsStr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- A reply with a header named `name`, case-insensitively. -/
def hasHeader (r : Reply) (name : String) (value : String) : Bool :=
  r.headers.any fun (k, v) => k.toLower == name.toLower && v == value

/-- Routes for exercising the router. -/
def testRoutes : List Route := [
  .mk' .get "/hello/:name" fun _ r => return .text s!"hello {(r.param "name").getD "?"}",
  .mk' .post "/hello/:name" fun _ _ => return .noContent,
  .mk' .post "/token" (csrf := .exempt) fun _ r =>
    return .text (toString (r.cookie sessionCookieName).isSome),
  .mk' .get "/boom" fun _ _ => throw (.userError "secret internals")
]

/-- The router, and the real route table, without a socket. -/
def routerTests : IO Unit := withCtx fun ctx _ => do
  group "http: router"
  let get (p : String) := dispatch testRoutes ctx (Req.mk' .get p)
  let r ← get "/hello/world"
  checkEq "a route answers" r.bodyText "hello world"
  check "with the security headers" (hasHeader r "X-Content-Type-Options" "nosniff" &&
    hasHeader r "Referrer-Policy" "no-referrer" &&
    hasHeader r "Content-Security-Policy" contentSecurityPolicy)
  check "the CSP forbids framing" ((contentSecurityPolicy.splitOn "; ").contains
    "frame-ancestors 'none'")
  check "and no-store" (hasHeader r "Cache-Control" "no-store")
  checkEq "an unknown path is 404" (← get "/nope").status.toCode 404
  checkEq "a dot-dot path is 404" (← get "/hello/../hello/x").status.toCode 404
  let put ← dispatch testRoutes ctx (Req.mk' .put "/hello/x")
  checkEq "a known path with another method is 405" put.status.toCode 405
  checkEq "with Allow" (put.header "Allow") (some "GET, POST")
  let post (hs : List (String × String)) := dispatch testRoutes ctx (Req.mk' .post "/hello/x" hs)
  checkEq "a POST without Origin is refused" (← post []).status.toCode 403
  checkEq "a cross-origin POST is refused"
    (← post [("Origin", "https://evil.example")]).status.toCode 403
  checkEq "a same-origin POST is answered"
    (← post [("Origin", "https://auth.example.org")]).status.toCode 204
  checkEq "an exempt route needs no Origin"
    (← dispatch testRoutes ctx (Req.mk' .post "/token")).status.toCode 200
  checkEq "and never sees the session cookie"
    (← dispatch testRoutes ctx (Req.mk' .post "/token" [("Cookie", "__Host-pyle=abc")])).bodyText
    "false"
  check "an https issuer gets HSTS"
    (hasHeader r "Strict-Transport-Security" "max-age=63072000; includeSubDomains")
  let plain : Ctx := { ctx with config := { ctx.config with issuer := "http://localhost:8420" } }
  check "a plain-http development issuer does not"
    (!(← dispatch testRoutes plain (Req.mk' .get "/hello/x")).headers.any
      (·.1 == "Strict-Transport-Security"))
  let boom ← get "/boom"
  checkEq "an exception is a 500" boom.status.toCode 500
  check "that says nothing of why" (!containsStr boom.bodyText "secret")
  check "and still has the headers" (hasHeader boom "X-Frame-Options" "DENY")
  let h ← Server.route ctx (Req.mk' .get "/healthz")
  checkEq "healthz answers" h.status.toCode 200
  checkEq "healthz says ok" h.bodyText "{\"status\":\"ok\"}"

/-- Read from a socket until the peer closes it. -/
partial def readAll (c : Std.Async.TCP.Socket.Client) (acc : ByteArray := .empty) :
    Std.Async.Async ByteArray := do
  match ← c.recv? 4096 with
  | some chunk => if chunk.isEmpty then return acc else readAll c (acc ++ chunk)
  | none => return acc

/-- Start the real server on a free port and ask it something over TCP. -/
def socketTests : IO Unit := withCtx fun ctx _ => do
  group "http: over a socket"
  let (port, stop) ← Server.serve ctx
  check "a port was bound" (port != 0)
  let response ← Std.Async.Async.block do
    let c ← Std.Async.TCP.Socket.Client.mk
    c.connect (.v4 { addr := (Std.Net.IPv4Addr.ofString "127.0.0.1").get!, port })
    c.send ("GET /healthz HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n".toUTF8)
    readAll c
  let text := (String.fromUTF8? response).getD ""
  check "the status line is 200" (text.startsWith "HTTP/1.1 200") text
  check "the body is the health answer" (text.endsWith "{\"status\":\"ok\"}") text
  check "the security headers are on the wire"
    (text.toLower.splitOn "\r\n" |>.contains "x-content-type-options: nosniff") text
  stop

/-- The mode bits of a file. -/
def modeOf (p : System.FilePath) : IO Nat := do
  let out ← IO.Process.output { cmd := "stat", args := #["-c", "%a", p.toString] }
  return out.stdout.trimAscii.toString.toNat!

/-- The root key and the database are created private. -/
def fileModeTests : IO Unit := IO.FS.withTempDir fun dir => do
  group "server: file modes"
  let key := dir / "root.key"
  Server.createRootKey key
  checkEq "the root key is 32 bytes" (← IO.FS.readBinFile key).size 32
  checkEq "the root key is mode 600" (← modeOf key) 600
  check "an existing key is never replaced" (← throws (Server.createRootKey key))
  let target := dir / "elsewhere"
  let link := dir / "link.key"
  discard <| IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  check "a planted symbolic link is refused" (← throws (Server.createRootKey link))
  check "and nothing was written through it" (!(← target.pathExists))
  Server.restrictFileModes
  let s ← Store.Store.openAt (dir / "pyle.db") 1
  discard <| s.addUser "alice" [] 1
  checkEq "the database is created mode 600" (← modeOf (dir / "pyle.db")) 600

/-- HTTP. -/
def httpTests : IO Unit := do
  cookieTests
  bodyTests
  securityTests
  rateLimitTests
  routerTests
  socketTests
  fileModeTests

end PyleTests