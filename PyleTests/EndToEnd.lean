import PyleTests.Oidc

/-!
# End to end, over a socket

Every other suite calls `Server.route` directly.  This one starts the server
the way `pyle serve` does, with `Server.serve` on port zero, and drives the
core of OpenID Connect over a real TCP connection: sign-in with a passkey, the
authorization request, the code exchange, the ID token checked against the
JWKS the server publishes, userinfo with the access token, and refresh-token
rotation and reuse.  What this adds over the other suites is the `Std.Http`
adapter in between: the request line, headers and body as they arrive on the
wire, and the reply as it leaves.

The client is a few lines of HTTP/1.1, one connection per request, written
here rather than taken from a library so that nothing between the test and
the socket is pyle's.  `scripts/integration.sh` covers the rest of the
protocols against the built binary.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open Lean (Json)
open Std.Net Std.Async

/-- Where the bytes `needle` first occur in `hay`, if they do. -/
def findBytes (hay needle : ByteArray) : Option Nat :=
  (List.range (hay.size + 1 - needle.size)).find? fun i =>
    (List.range needle.size).all fun j => hay.get! (i + j) == needle.get! j

/-- A hexadecimal number. -/
def hexValue? (s : String) : Option Nat :=
  if s.isEmpty then none else
  s.foldl (init := some 0) fun acc c => do
    let n ← acc
    let c := c.toLower
    let d ← if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else none
    return n * 16 + d

/-- The body of a `chunked` transfer coding, once it is complete. -/
partial def dechunk (b : ByteArray) (acc : ByteArray := .empty) : Option ByteArray := do
  let eol ← findBytes b "\r\n".toUTF8
  let line ← String.fromUTF8? (b.extract 0 eol)
  let size ← hexValue? ((line.splitOn ";").headD "").trimAscii.toString
  if size == 0 then return acc
  let start := eol + 2
  guard (b.size ≥ start + size + 2)
  dechunk (b.extract (start + size + 2) b.size) (acc ++ b.extract start (start + size))

/-- A reply read off the wire: the status line, the headers and the body. -/
def parseWire (raw : ByteArray) : Except String Reply := do
  let some sep := findBytes raw "\r\n\r\n".toUTF8 | throw "no end of headers"
  let some head := String.fromUTF8? (raw.extract 0 sep) | throw "headers not UTF-8"
  let lines := head.splitOn "\r\n"
  let code ← match ((lines.headD "").splitOn " ")[1]? >>= (·.toNat?) with
    | some c => pure c
    | none => throw s!"bad status line '{lines.headD ""}'"
  let some status := Std.Http.Status.ofCode none code.toUInt16 | throw s!"bad status {code}"
  let headers := lines.drop 1 |>.filterMap fun l =>
    match l.splitOn ":" with
    | k :: v => some (k, (":".intercalate v).trimAscii.toString)
    | [] => none
  let rest := raw.extract (sep + 4) raw.size
  let chunked := headers.any fun (k, v) =>
    k.toLower == "transfer-encoding" && v.toLower == "chunked"
  let body ← if chunked then
      match dechunk rest with
      | some b => pure b
      | none => throw "incomplete chunked body"
    else pure rest
  return { status, headers, body }

/-- Whether `raw` holds a whole reply: the headers, and as much body as they
announce. -/
def wireComplete (raw : ByteArray) : Bool := Id.run do
  let some sep := findBytes raw "\r\n\r\n".toUTF8 | return false
  let head := (String.fromUTF8? (raw.extract 0 sep)).getD ""
  let rest := raw.extract (sep + 4) raw.size
  let fields := (head.splitOn "\r\n").drop 1 |>.map fun l =>
    match l.splitOn ":" with
    | k :: v => (k.toLower, (":".intercalate v).trimAscii.toString.toLower)
    | [] => ("", "")
  if fields.any (· == ("transfer-encoding", "chunked")) then
    return (dechunk rest).isSome
  match (fields.lookup "content-length").bind (·.toNat?) with
  | some n => return rest.size ≥ n
  | none => return false

/-- One request on a fresh connection to `127.0.0.1:port`, read until the
reply is whole or the server closes. -/
def wire (port : UInt16) (method target : String) (headers : List (String × String) := [])
    (body : ByteArray := .empty) : IO Reply := do
  let head := s!"{method} {target} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\n" ++
    String.join (headers.map fun (k, v) => s!"{k}: {v}\r\n") ++
    s!"Content-Length: {body.size}\r\nConnection: close\r\n\r\n"
  let raw ← Async.block do
    let s ← TCP.Socket.Client.mk
    s.connect (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port })
    s.send (head.toUTF8 ++ body)
    let mut acc := ByteArray.empty
    for _ in [0:4096] do
      if wireComplete acc then break
      match ← s.recv? 65536 with
      | some b => acc := acc ++ b
      | none => break
    return acc
  IO.ofExcept (parseWire raw |>.mapError IO.userError)

/-- A form `POST` over the socket. -/
def wireForm (port : UInt16) (path : String) (form : List (String × String))
    (headers : List (String × String) := []) : IO Reply :=
  wire port "POST" path ([("Content-Type", "application/x-www-form-urlencoded")] ++ headers)
    (queryString form).toUTF8

/-- A JSON `POST` from the issuer's origin over the socket. -/
def wireJson (port : UInt16) (path : String) (body : Json) : IO Reply :=
  wire port "POST" path [("Origin", issuer), ("Content-Type", "application/json")]
    body.compress.toUTF8

/-- Verify an ES256 ID token against the JWKS the server serves on `port`. -/
def wireVerify (port : UInt16) (token : String) : IO (Except String Json) := do
  let some header := jwsHeader token | return .error "no header"
  let .ok kid := header.getObjValAs? String "kid" | return .error "no kid"
  let .ok keys := (bodyJson (← wire port "GET" "/jwks")).getObjValAs? (Array Json) "keys"
    | return .error "no JWKS"
  let some jwk := keys.find? (·.getObjValAs? String "kid" == .ok kid)
    | return .error "the kid is not in the JWKS"
  let some key := jwkP256 jwk | return .error "not a P-256 JWK"
  return Jwt.verify .es256 key token

/-- The authorization-code flow over a socket. -/
def endToEndTests : IO Unit := withCtx fun ctx _ => do
  group "end to end: OpenID Connect over a socket"
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let (secret, _) ← addClients ctx
  let (port, stop) ← Server.serve ctx
  try
    check "the server binds a port of its own" (port != 0)
    let h ← wire port "GET" "/healthz"
    checkEq "/healthz answers" h.status.toCode 200
    check "with the security headers" ((h.header "Content-Security-Policy").isSome)
    let d ← wire port "GET" "/.well-known/openid-configuration"
    checkEq "discovery names the issuer" (jsonStr d "issuer") (some issuer)
    -- A passkey signs in.
    let k ← SoftKey.new
    enrol ctx alice k
    let b ← wireJson port "/signin/webauthn/begin" emptyObj
    checkEq "a sign-in ceremony begins" b.status.toCode 200
    let f ← wireJson port "/signin/webauthn/finish"
      (Json.mkObj [("credential", ← k.assert (bodyJson b))])
    checkEq "the passkey signs in" f.status.toCode 200
    let some cookie := sessionCookieOf f | check "and sets the session cookie" false
    let session := [("Cookie", s!"{sessionCookieName}={cookie}")]
    -- The authorization request, with the session.
    let a ← wire port "GET" (authorizeUrl "app") session
    checkEq "the authorization request redirects" a.status.toCode 303
    check "to the client" ((location a).startsWith (appRedirect ++ "?"))
    checkEq "with the state" (param (location a) "state") (some "st4te")
    checkEq "and iss" (param (location a) "iss") (some issuer)
    let some code := param (location a) "code" | check "with a code" false
    -- The exchange.
    let t ← wireForm port "/token" [("grant_type", "authorization_code"), ("code", code),
      ("redirect_uri", appRedirect), ("code_verifier", pkce.1)] (basic "app" secret)
    checkEq "the code exchanges" t.status.toCode 200
    check "not to be cached" ((t.header "Cache-Control") == some "no-store")
    let some idToken := jsonStr t "id_token" | check "an ID token" false
    let some access := jsonStr t "access_token" | check "an access token" false
    let some refresh := jsonStr t "refresh_token" | check "a refresh token" false
    match ← wireVerify port idToken with
    | .error e => check "the ID token verifies against the served JWKS" false e
    | .ok claims =>
      check "the ID token verifies against the served JWKS" true
      checkEq "its subject is alice's handle" (claims.getObjValAs? String "sub" |>.toOption)
        (some (Jose.b64urlEncode alice.handle))
      checkEq "and the nonce comes back" (claims.getObjValAs? String "nonce" |>.toOption)
        (some "n0nce")
    let again ← wireForm port "/token" [("grant_type", "authorization_code"), ("code", code),
      ("redirect_uri", appRedirect), ("code_verifier", pkce.1)] (basic "app" secret)
    checkEq "a code is good once" (jsonStr again "error") (some "invalid_grant")
    -- userinfo with the biscuit.
    let u ← wire port "GET" "/userinfo" [("Authorization", s!"Bearer {access}")]
    checkEq "userinfo answers the access token" u.status.toCode 200
    checkEq "for alice" (jsonStr u "name") (some "alice")
    let u ← wire port "GET" "/userinfo"
    checkEq "and nothing without it" u.status.toCode 401
    -- Refresh rotation and reuse.  The code's second use revoked the first
    -- family, so a new code starts one.
    let a ← wire port "GET" (authorizeUrl "app") session
    let t ← wireForm port "/token" [("grant_type", "authorization_code"),
      ("code", (param (location a) "code").getD ""), ("redirect_uri", appRedirect),
      ("code_verifier", pkce.1)] (basic "app" secret)
    let some refresh1 := jsonStr t "refresh_token" | check "a second family" false
    let refreshWith (rt : String) := wireForm port "/token"
      [("grant_type", "refresh_token"), ("refresh_token", rt)] (basic "app" secret)
    checkEq "the first family is revoked" (jsonStr (← refreshWith refresh) "error")
      (some "invalid_grant")
    let r2 ← refreshWith refresh1
    checkEq "the refresh token rotates" r2.status.toCode 200
    let some refresh2 := jsonStr r2 "refresh_token" | check "to a new one" false
    check "to a new value" (refresh2 != refresh1)
    checkEq "reusing the old one is refused" (jsonStr (← refreshWith refresh1) "error")
      (some "invalid_grant")
    checkEq "and revokes the family" (jsonStr (← refreshWith refresh2) "error")
      (some "invalid_grant")
  finally
    stop

end PyleTests