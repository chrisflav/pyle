import PyleTests.Device

/-!
# Forward authentication

`/forward-auth` as Caddy or Traefik asks it, through `Server.route`: only a
trusted proxy is answered; a protected host's request without a cookie is sent
round through `/forward-auth/grant` and the callback that sets the host's
cookie; with the cookie the request is allowed or refused by the host's
datalog policy; and ending the session ends it everywhere.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open Pyle.ForwardAuth (stateHash)

/-- The proxy's address in these tests. -/
def proxy : String := "10.0.0.1"

/-- A context protecting `app.example.org` for the group `admin` and, on
`wiki.example.org`, everyone except on `/admin`. -/
def withForwardAuth (ctx : Ctx) : Ctx :=
  { ctx with config := { ctx.config with
      trustedProxies := [proxy],
      forwardAuthHosts := [("app.example.org", "allow if group(\"admin\");"),
        ("wiki.example.org",
          "deny if path($p), $p.starts_with(\"/admin\");\nallow if user($u);")] } }

/-- A forward-auth request from the proxy about `method host uri`. -/
def askProxy (ctx : Ctx) (host uri : String) (method : String := "GET")
    (cookies : List String := []) (peer : String := proxy) : IO Reply :=
  Server.route ctx { Req.mk' .get "/forward-auth"
    ([("X-Forwarded-Host", host), ("X-Forwarded-Uri", uri), ("X-Forwarded-Method", method),
      ("X-Forwarded-Proto", "https")] ++
      (if cookies.isEmpty then [] else [("Cookie", "; ".intercalate cookies)]))
    (clientAddress := peer) with peer }

/-- Every cookie a reply sets, as `name=value`. -/
def setCookies (r : Reply) : List String :=
  r.headers.filterMap fun (k, v) =>
    if k.toLower == "set-cookie" then (v.splitOn ";").head? else none

/-- The cookie of a name a reply sets, as `name=value`. -/
def cookieSet (r : Reply) (name : String) : Option String :=
  (setCookies r).find? (·.startsWith (name ++ "="))

/-- The protected host's cookie a reply sets, as `name=value`. -/
def forwardCookie (r : Reply) : Option String := cookieSet r ForwardAuth.cookieName

/-- Begin at a protected host, go through the grant with a pyle session, and
come back to the callback with the state cookie; the callback's reply. -/
def throughGrant (ctx : Ctx) (session host uri : String) (keepState : Bool := true) :
    IO Reply := do
  let r ← askProxy ctx host uri
  let state := (cookieSet r ForwardAuth.stateCookieName).getD ""
  let g ← get ctx (location r |>.drop issuer.length |>.toString) session
  let rest := ((location g).splitOn host)[1]?.getD ""
  askProxy ctx host rest (cookies := if keepState then [state] else [])

/-- Sign in through the grant and the callback; the host's cookie. -/
def forwardSignIn (ctx : Ctx) (session host uri : String) : IO (Option String) :=
  return forwardCookie (← throughGrant ctx session host uri)

/-- The policy as a function. -/
def policyTests : IO Unit := do
  group "forward-auth: policies"
  let p := "allow if group(\"admin\");"
  check "a group allows" (ForwardAuth.allows p "alice" ["admin"] "h" "/" "GET")
  check "another refuses" (!ForwardAuth.allows p "bob" ["staff"] "h" "/" "GET")
  let q := "deny if method(\"DELETE\");\nallow if user($u), host(\"h\");"
  check "facts about the request" (ForwardAuth.allows q "bob" [] "h" "/x" "GET")
  check "deny first" (!ForwardAuth.allows q "bob" [] "h" "/x" "DELETE")
  check "nothing matching refuses" (!ForwardAuth.allows q "bob" [] "other" "/x" "GET")
  check "a policy that does not parse refuses" (!ForwardAuth.allows "allow if" "a" [] "h" "/" "GET")
  let key ← Crypto.randomBytes 32
  let h := Store.SecretHash.of "s".toUTF8
  let c := ForwardAuth.encodeCookie key h "app.example.org" 100
  check "a cookie names its session" (ForwardAuth.decodeCookie key c "app.example.org" 99 == some h)
  check "only for its host" (ForwardAuth.decodeCookie key c "wiki.example.org" 99).isNone
  check "only until it expires" (ForwardAuth.decodeCookie key c "app.example.org" 100).isNone
  check "only under its key"
    (ForwardAuth.decodeCookie (← Crypto.randomBytes 32) c "app.example.org" 99).isNone
  let tampered := "A" ++ (c.drop 1).toString
  check "and not altered" (ForwardAuth.decodeCookie key tampered "app.example.org" 99).isNone

/-- Path normalisation and safe redirects, as functions. -/
def pathTests : IO Unit := do
  group "forward-auth: paths"
  for raw in ["//admin/x", "/./admin/x", "/x/../admin/x", "/%61dmin/x", "/%2E/admin/x",
      "/x/%2e%2e/admin/x", "///admin//x"] do
    checkEq s!"{raw} is /admin/x" (ForwardAuth.normalisePath raw) (some "/admin/x")
  checkEq "a trailing slash is kept" (ForwardAuth.normalisePath "/a/b/") (some "/a/b/")
  checkEq "other escapes are kept" (ForwardAuth.normalisePath "/a%20b") (some "/a%20b")
  for raw in ["/a%2Fb", "/a%2fb", "/a%5Cb", "/a\\b", "/a\x01b", "a/b", "/a..b", "/a%00b"] do
    checkEq s!"{raw} is refused" (ForwardAuth.normalisePath raw) none
  check "/x?q is safe to go back to" (ForwardAuth.safeRedirectPath "/x?q=1")
  for p in ["//evil.example/phish", "/\\evil", "x", "/a\\b", "/a\nb"] do
    check s!"{p} is not" (!ForwardAuth.safeRedirectPath p)

/-- The flow through the proxy. -/
def proxyTests : IO Unit := withCtx fun ctx0 _ => do
  group "forward-auth: through the proxy"
  let ctx := withForwardAuth ctx0
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let bob ← ctx.store.addUser "bob" ["staff"] 1
  let r ← askProxy ctx "app.example.org" "/" (peer := "10.9.9.9")
  checkEq "an untrusted peer is refused" r.status.toCode 403
  let r ← askProxy ctx "elsewhere.example.org" "/"
  checkEq "a host not listed is refused" r.status.toCode 403
  let r ← askProxy ctx "app.example.org" "/reports?q=1"
  checkEq "no cookie: 302" r.status.toCode 302
  check "to the grant, with the original URL"
    ((location r).startsWith (s!"{issuer}/forward-auth/grant?" ++
      queryString [("rd", "https://app.example.org/reports?q=1")] ++ "&state="))
  check "setting a state cookie on the host" (cookieSet r ForwardAuth.stateCookieName).isSome
  let r ← askProxy ctx "app.example.org" "/api" "POST"
  checkEq "a POST without a cookie: 401" r.status.toCode 401
  let r ← askProxy ctx "app.example.org" "/a%2Fb"
  checkEq "a path pyle cannot read the same way as the service: 400" r.status.toCode 400
  -- The grant, on pyle's host.
  let aliceSession ← signedIn ctx alice
  let begun ← askProxy ctx "app.example.org" "/reports?q=1"
  let grantPath := (location begun).drop issuer.length |>.toString
  let g ← get ctx grantPath
  check "the grant without a session sends to sign in" ((location g).startsWith "/signin?")
  let g ← get ctx grantPath aliceSession
  check "with one, to the host's callback with a code"
    ((location g).startsWith "https://app.example.org/.pyle/forward-auth?code=")
  let st := stateHash "x"
  let grantFor (rd : String) := get ctx
    s!"/forward-auth/grant?{queryString [("rd", rd), ("state", st)]}" aliceSession
  checkEq "the grant refuses a host it does not protect"
    (← grantFor "https://evil.example/").status.toCode 403
  for rd in ["https://app.example.org//evil.example/phish", "https://app.example.org/\\evil",
      "https://app.example.org/a\\b"] do
    let g ← grantFor rd
    checkEq s!"the grant refuses {rd}" g.status.toCode 400
    check "without redirecting" (g.header "location").isNone
  let g ← get ctx s!"/forward-auth/grant?{queryString [("rd", "https://app.example.org/")]}"
    aliceSession
  checkEq "the grant refuses a request without state" g.status.toCode 400
  -- Opening a double-slash path directly goes round on the same host.
  let r ← askProxy ctx "app.example.org" "//evil.example/phish"
  check "a double-slash path stays on the host"
    ((param (location r) "rd") == some "https://app.example.org/evil.example/phish")
  -- The callback, through the proxy, with the state cookie.
  let state := (cookieSet begun ForwardAuth.stateCookieName).getD ""
  let callback := ((location g).splitOn "app.example.org")[1]?.getD ""
  let g ← get ctx grantPath aliceSession
  let callback := if callback.isEmpty then ((location g).splitOn "app.example.org")[1]?.getD ""
    else callback
  let c ← askProxy ctx "app.example.org" callback (cookies := [state])
  checkEq "the callback answers 302" c.status.toCode 302
  checkEq "back to where the user was going" (location c) "/reports?q=1"
  let some cookie := forwardCookie c | check "and sets the host's cookie" false
  check "and sets the host's cookie" (cookie.startsWith "__Host-pyle-forward=")
  check "and clears the state" (cookieSet c ForwardAuth.stateCookieName ==
    some s!"{ForwardAuth.stateCookieName}=")
  check "HttpOnly" (((c.header "set-cookie").getD "").splitOn "; " |>.contains "HttpOnly")
  let again ← askProxy ctx "app.example.org" callback (cookies := [state])
  check "a code is good once" (forwardCookie again).isNone
  -- Login CSRF: a code redeemed in a browser that did not begin the sign-in.
  let planted ← throughGrant ctx aliceSession "app.example.org" "/" (keepState := false)
  checkEq "a code without the state cookie is refused" planted.status.toCode 403
  check "and sets nothing" (forwardCookie planted).isNone
  let r ← askProxy ctx "app.example.org" "/"
  let wrong := (cookieSet r ForwardAuth.stateCookieName).getD ""
  let g ← get ctx ((location (← askProxy ctx "app.example.org" "/")).drop issuer.length
    |>.toString) aliceSession
  let c ← askProxy ctx "app.example.org" (((location g).splitOn "app.example.org")[1]?.getD "")
    (cookies := [wrong])
  checkEq "nor with another sign-in's state" c.status.toCode 403
  -- With the cookie.
  let r ← askProxy ctx "app.example.org" "/reports" (cookies := [cookie])
  checkEq "alice is let through" r.status.toCode 200
  check "as Remote-User" (hasHeader r "Remote-User" "alice")
  check "with Remote-Groups" (hasHeader r "Remote-Groups" "admin")
  check "and no Remote-Email" (r.header "remote-email").isNone
  let r ← askProxy ctx "wiki.example.org" "/" (cookies := [cookie])
  checkEq "the cookie is for its host only" r.status.toCode 302
  -- Bob is signed in but not allowed on app.
  let bobSession ← signedIn ctx bob
  let r ← askProxy ctx "app.example.org" "/reports?q=1"
  let g ← get ctx ((location r).drop issuer.length |>.toString) bobSession
  checkEq "bob is refused at the grant" g.status.toCode 403
  let key := ForwardAuth.macKey ctx.rootKey
  let bobHash := Store.SecretHash.of ((Session.decodeId bobSession).getD .empty)
  let forged := s!"{ForwardAuth.cookieName}=" ++
    ForwardAuth.encodeCookie key bobHash "app.example.org" ((← ctx.clock) + 100)
  let r ← askProxy ctx "app.example.org" "/" (cookies := [forged])
  checkEq "and by the policy even with a cookie" r.status.toCode 403
  -- The wiki: a path rule, and every way around it.
  let some wiki ← forwardSignIn ctx bobSession "wiki.example.org" "/page"
    | check "bob signs in to the wiki" false
  checkEq "bob may read the wiki" (← askProxy ctx "wiki.example.org" "/page" (cookies := [wiki])
    ).status.toCode 200
  for uri in ["/admin/x", "//admin/x", "/./admin/x", "/x/../admin/x", "/%61dmin/x",
      "/%2e/admin/x"] do
    checkEq s!"but not {uri}" (← askProxy ctx "wiki.example.org" uri (cookies := [wiki])
      ).status.toCode 403
  checkEq "and an escaped slash is not read at all" (← askProxy ctx "wiki.example.org"
    "/admin%2Fx" (cookies := [wiki])).status.toCode 400
  -- Signing out of pyle ends it everywhere.
  discard <| ctx.store.endSession (.of ((Session.decodeId aliceSession).getD .empty))
  let r ← askProxy ctx "app.example.org" "/reports" (cookies := [cookie])
  checkEq "once the session ends, the cookie is worthless" r.status.toCode 302

/-- The shared secret between the proxy and pyle. -/
def secretTests : IO Unit := withCtx fun ctx0 _ => do
  group "forward-auth: shared secret"
  let ctx := withForwardAuth ctx0
  let ctx := { ctx with
    config := { ctx.config with forwardAuthSecret := some "s3cret-s3cret-s3cret" } }
  let ask (headers : List (String × String)) := Server.route ctx { Req.mk' .get "/forward-auth"
    ([("X-Forwarded-Host", "app.example.org"), ("X-Forwarded-Uri", "/")] ++ headers)
    (clientAddress := proxy) with peer := proxy }
  checkEq "without the secret, refused" (← ask []).status.toCode 403
  checkEq "with a wrong one, refused" (← ask [("X-Pyle-Forward-Auth", "s3cret-s3cret-s3creT")]
    ).status.toCode 403
  checkEq "with it, answered" (← ask [("X-Pyle-Forward-Auth", "s3cret-s3cret-s3cret")]
    ).status.toCode 302

/-- Forward authentication. -/
def forwardAuthTests : IO Unit := do
  policyTests
  pathTests
  proxyTests
  secretTests

end PyleTests