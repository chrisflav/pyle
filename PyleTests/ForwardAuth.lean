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

/-- The protected host's cookie a reply sets, as `name=value`. -/
def forwardCookie (r : Reply) : Option String :=
  (r.header "set-cookie").bind fun c => (c.splitOn ";").head?

/-- Sign in through the grant and the callback; the host's cookie. -/
def forwardSignIn (ctx : Ctx) (session host uri : String) : IO (Option String) := do
  let r ← askProxy ctx host uri
  let some rd := param (location r) "rd" | return none
  let g ← get ctx s!"/forward-auth/grant?{queryString [("rd", rd)]}" session
  let callback := location g
  let some rest := (callback.splitOn host)[1]? | return none
  let c ← askProxy ctx host rest
  return forwardCookie c

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
  checkEq "to the grant, with the original URL" (location r)
    s!"{issuer}/forward-auth/grant?{queryString [("rd", "https://app.example.org/reports?q=1")]}"
  let r ← askProxy ctx "app.example.org" "/api" "POST"
  checkEq "a POST without a cookie: 401" r.status.toCode 401
  -- The grant, on pyle's host.
  let rd := "https://app.example.org/reports?q=1"
  let g ← get ctx s!"/forward-auth/grant?{queryString [("rd", rd)]}"
  check "the grant without a session sends to sign in" ((location g).startsWith "/signin?")
  let aliceSession ← signIn ctx alice.id ["hwk", "user"]
  let g ← get ctx s!"/forward-auth/grant?{queryString [("rd", rd)]}" aliceSession
  check "with one, to the host's callback with a code"
    ((location g).startsWith "https://app.example.org/.pyle/forward-auth?code=")
  let g2 ← get ctx s!"/forward-auth/grant?{queryString [("rd", "https://evil.example/")]}"
    aliceSession
  checkEq "the grant refuses a host it does not protect" g2.status.toCode 403
  -- The callback, through the proxy.
  let callback := ((location g).splitOn "app.example.org")[1]?.getD ""
  let c ← askProxy ctx "app.example.org" callback
  checkEq "the callback answers 302" c.status.toCode 302
  checkEq "back to where the user was going" (location c) "/reports?q=1"
  let some cookie := forwardCookie c | check "and sets the host's cookie" false
  check "and sets the host's cookie" (cookie.startsWith "__Host-pyle-forward=")
  check "HttpOnly" (((c.header "set-cookie").getD "").splitOn "; " |>.contains "HttpOnly")
  let again ← askProxy ctx "app.example.org" callback
  check "a code is good once" (again.header "set-cookie").isNone
  -- With the cookie.
  let r ← askProxy ctx "app.example.org" "/reports" (cookies := [cookie])
  checkEq "alice is let through" r.status.toCode 200
  check "as Remote-User" (hasHeader r "Remote-User" "alice")
  check "with Remote-Groups" (hasHeader r "Remote-Groups" "admin")
  check "and no Remote-Email" (r.header "remote-email").isNone
  let r ← askProxy ctx "wiki.example.org" "/" (cookies := [cookie])
  checkEq "the cookie is for its host only" r.status.toCode 302
  -- Bob is signed in but not allowed on app.
  let bobSession ← signIn ctx bob.id ["hwk", "user"]
  let g ← get ctx s!"/forward-auth/grant?{queryString [("rd", rd)]}" bobSession
  checkEq "bob is refused at the grant" g.status.toCode 403
  let key := ForwardAuth.macKey ctx.rootKey
  let bobHash := Store.SecretHash.of ((Session.decodeId bobSession).getD .empty)
  let forged := s!"{ForwardAuth.cookieName}=" ++
    ForwardAuth.encodeCookie key bobHash "app.example.org" ((← ctx.clock) + 100)
  let r ← askProxy ctx "app.example.org" "/" (cookies := [forged])
  checkEq "and by the policy even with a cookie" r.status.toCode 403
  -- The wiki: a path rule.
  let some wiki ← forwardSignIn ctx bobSession "wiki.example.org" "/page"
    | check "bob signs in to the wiki" false
  checkEq "bob may read the wiki" (← askProxy ctx "wiki.example.org" "/page" (cookies := [wiki])
    ).status.toCode 200
  checkEq "but not its admin pages" (← askProxy ctx "wiki.example.org" "/admin/x"
    (cookies := [wiki])).status.toCode 403
  -- Signing out of pyle ends it everywhere.
  discard <| ctx.store.endSession (.of ((Session.decodeId aliceSession).getD .empty))
  let r ← askProxy ctx "app.example.org" "/reports" (cookies := [cookie])
  checkEq "once the session ends, the cookie is worthless" r.status.toCode 302

/-- Forward authentication. -/
def forwardAuthTests : IO Unit := do
  policyTests
  proxyTests

end PyleTests