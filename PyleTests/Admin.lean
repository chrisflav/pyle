import PyleTests.Hardening

/-!
# The administration pages

Through `Server.route`, as the other page tests: who may see `/admin` at all
(the authorization matrix — no session, not an administrator, a disabled
one, below `phr`, at `phr` without a fresh sign-in, fresh), the `Origin`
check on every endpoint, the last administrator, what each action does and
what the audit log says of it, escaping of hostile names and addresses, and
the secrets that are shown once and never again.
-/

namespace PyleTests

open Pyle Pyle.Http
open Lean (Json toJson)

/-- A limiter of its own, so that the refusals one check provokes on purpose
do not slow down the next: the rate limit has a test of its own. -/
def fresh (ctx : Ctx) : IO Ctx := return { ctx with limiter := ← RateLimiter.new }

/-- An administrator's change, as the pages post it, with a limiter of its
own (`fresh`). -/
def adminPost (ctx : Ctx) (path : String) (body : List (String × Json)) (cookie : String) :
    IO Reply := do
  postJson (← fresh ctx) path (Json.mkObj body) (some cookie)

/-- Every `POST` route under `/admin`. -/
def adminPosts : List String :=
  Admin.routes.filterMap fun rt =>
    if rt.method == .post then
      some ("/" ++ "/".intercalate (rt.pattern.map fun
        | .lit s => s
        | .param _ => "x"))
    else none

/-- Every `GET` page under `/admin` an administrator can open, given an
account and a client that exist. -/
def adminPages (user client : String) : List String :=
  ["/admin", s!"/admin/users/{user}", "/admin/invitations", "/admin/clients",
   s!"/admin/clients/{client}", "/admin/audit", "/admin/audit?page=2", "/admin/keys"]

/-- The audit entries made by `actor`, as (event, outcome, detail). -/
def auditBy (ctx : Ctx) (actor : String) : IO (List (String × String × String)) :=
  return (← Audit.entries ctx.store).toList.filterMap fun e =>
    if e.userName == some actor then some (e.event, e.outcome, e.detail) else none

/-- Whether `actor` has an entry for `event` with `outcome` whose detail
starts with `start`. -/
def audited (ctx : Ctx) (actor event outcome start : String) : IO Bool :=
  return (← auditBy ctx actor).any fun (e, o, d) => e == event && o == outcome && d.startsWith start

/-- A two-factor session below `phr`: a security key that does not verify the
user, and a code. -/
def mfaSession (ctx : Ctx) (u : Store.User) : IO String := do
  let sk ← SoftKey.new (uv := false)
  enrol ctx u sk
  let secret ← giveTotp ctx u
  let r ← signInVia (← fresh ctx) sk (beginBody := Json.mkObj [("name", Json.str u.name)])
    (extra := [("totp", Json.str (totpAt secret (← ctx.clock)))])
  let some id := sessionCookieOf r
    | throw (.userError s!"mfaSession: the sign-in failed: {r.bodyText}")
  return id

/-- Who may see the pages, and with what session. -/
def adminAccessTests : IO Unit := withCtx fun ctx clock => do
  group "admin: who may"
  let nothing ← getPage ctx "/nothing-here"
  let same (r : Reply) : Bool :=
    r.status.toCode == 404 && r.bodyText == nothing.bodyText &&
      r.contentType == nothing.contentType
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, rk) ← sessionFor ctx root
  let bob ← ctx.store.addUser "bob" ["staff"] 1
  let (bid, _) ← sessionFor ctx bob
  -- No session at all.
  for p in adminPages "bob" "none" ++ ["/admin/assets/admin.js", "/admin/nothing",
      "/admin/users/bob/more", "//admin", "/admin/"] do
    check s!"without a session, GET {p} is the 404 of nothing" (same (← getPage ctx p))
  for p in adminPosts do
    check s!"without a session, POST {p} is the 404 of nothing"
      (same (← postJson ctx p (Json.mkObj [("name", "root")])))
  check "even from another origin, where the Origin check would say 403"
    (same (← postJson ctx "/admin/users/disable" emptyObj (origin := "https://evil.example")))
  check "and for a method no route takes, where the router would say 405"
    (same (← postJson ctx "/admin" emptyObj))
  -- An account that is not an administrator.
  for p in adminPages "bob" "none" ++ ["/admin/assets/admin.js"] do
    check s!"for a non-administrator, GET {p} is the 404 of nothing"
      (same (← getPage ctx p (some bid)))
  for p in adminPosts do
    check s!"for a non-administrator, POST {p} is the 404 of nothing"
      (same (← adminPost ctx p [("name", "root"), ("confirm", "root")] bid))
  check "a non-administrator's 405 is a 404 too" (same (← postJson ctx "/admin" emptyObj bid))
  check "and the account page does not mention the pages"
    (!containsStr (← getPage ctx "/account" bid).bodyText "/admin")
  checkEq "nothing was changed" ((← ctx.store.findUserByName "root").map (·.disabled))
    (some false)
  -- An administrator, freshly signed in with a passkey.
  let page ← getPage ctx "/admin" rid
  checkEq "an administrator gets the accounts page" page.status.toCode 200
  check "which lists both accounts"
    (containsStr page.bodyText ">root</a>" && containsStr page.bodyText ">bob</a>")
  check "the account page links to it, for an administrator"
    (containsStr (← getPage ctx "/account" rid).bodyText "<a id=\"admin-link\" href=\"/admin\">")
  let js ← getPage ctx "/admin/assets/admin.js" rid
  checkEq "the script is served to an administrator" (js.status.toCode, js.bodyText)
    (200, Admin.script)
  let ok ← adminPost ctx "/admin/users/groups" [("name", "bob"), ("groups", toJson ["staff"])] rid
  checkEq "and a fresh administrator may change things" ok.status.toCode 200
  -- At phr, but not within the step-up window.
  clock.modify (· + SignIn.stepUpSeconds + 1)
  checkEq "an older passkey session still sees the pages" (← getPage ctx "/admin" rid).status.toCode
    200
  for p in adminPosts do
    let r ← adminPost ctx p [("name", "bob")] rid
    checkEq s!"but POST {p} needs a fresh sign-in" (r.status.toCode, errorOf r)
      (403, "step_up_required")
  let up ← stepUpVia ctx rk (some rid)
  let some rid := sessionCookieOf up | check "the step-up gives a cookie" false
  let ok ← adminPost ctx "/admin/users/enable" [("name", "bob")] rid
  checkEq "after a step-up with the passkey, it may" ok.status.toCode 204
  -- An administrator below phr.
  let mia ← ctx.store.addUser "mia" ["admin"] 1
  let mid ← mfaSession ctx mia
  let r ← getPage ctx "/admin/users/bob" (some mid)
  checkEq "an administrator signed in below phr is sent to sign in at phr"
    (r.status.toCode, r.header "Location")
    (303, some "/signin?return=%2Fadmin%2Fusers%2Fbob&acr=phr")
  let signin ← getPage ctx "/signin?return=%2Fadmin%2Fusers%2Fbob&acr=phr" mid
  check "where only a passkey is offered"
    (signin.status.toCode == 200 && containsStr signin.bodyText "data-mode=\"stepup\"" &&
      !containsStr signin.bodyText "id=\"other\"")
  let r ← adminPost ctx "/admin/users/enable" [("name", "bob")] mid
  checkEq "and is answered step_up_required by an endpoint, though freshly signed in"
    (r.status.toCode, errorOf r) (403, "step_up_required")
  checkEq "the script is still hers" (← getPage ctx "/admin/assets/admin.js" mid).status.toCode
    200
  -- A disabled administrator, and one taken out of the group.
  discard <| ctx.store.setUserDisabled mia.id true (← clock.get)
  let zoe ← ctx.store.addUser "zoe" ["admin"] 1
  let mid2 ← sessionFor ctx zoe
  discard <| ctx.store.setUserDisabled zoe.id true (← clock.get)
  check "a disabled administrator's session is the 404 of nothing"
    (same (← getPage ctx "/admin" mid2.1) && same (← getPage ctx "/admin" mid))
  check "and its posts too"
    (same (← adminPost ctx "/admin/users/enable" [("name", "zoe")] mid2.1))
  let ann ← ctx.store.addUser "ann" ["admin"] 1
  let (aid, _) ← sessionFor ctx ann
  checkEq "ann is an administrator" (← getPage ctx "/admin" aid).status.toCode 200
  discard <| ctx.store.setUserGroups ann.id ["staff"]
  check "and not once she is out of the group" (same (← getPage ctx "/admin" aid))
  -- Another administrator group.
  let ops := { ctx with config := { ctx.config with adminGroup := "ops" } }
  check "with adminGroup ops, the admin group is nothing special"
    (same (← getPage ops "/admin" rid))
  discard <| ctx.store.setUserGroups bob.id ["ops"]
  checkEq "and ops is" (← getPage ops "/admin" bid).status.toCode 200

/-- The `Origin` check on every endpoint. -/
def adminOriginTests : IO Unit := withCtx fun ctx _ => do
  group "admin: the Origin check"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  discard <| ctx.store.addUser "bob" [] 1
  for p in adminPosts do
    let evil ← postJson (← fresh ctx) p (Json.mkObj [("name", "bob")]) (some rid)
      (origin := "https://evil.example")
    checkEq s!"POST {p} from another origin is refused" (evil.status.toCode, errorOf evil)
      (403, "forbidden")
    let none_ ← Server.route (← fresh ctx) (Req.mk' .post p
      ([("Content-Type", "application/json")] ++ cookieHeader (some rid))
      (Json.mkObj [("name", "bob")]).compress.toUTF8 "198.51.100.7")
    checkEq s!"and without an Origin" none_.status.toCode 403
    let null ← postJson (← fresh ctx) p (Json.mkObj [("name", "bob")]) (some rid)
      (origin := "null")
    checkEq s!"and from the null origin" null.status.toCode 403
  checkEq "bob is untouched" ((← ctx.store.findUserByName "bob").map (·.disabled)) (some false)
  check "the POST routes take part in the check"
    (Admin.routes.all fun rt => rt.csrf == .checkOrigin)

/-- The last enabled administrator. -/
def lastAdminTests : IO Unit := withCtx fun ctx _ => do
  group "admin: the last administrator"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let last (r : Reply) : Bool := r.status.toCode == 409 && errorOf r == "last_administrator"
  check "the only administrator cannot disable herself"
    (last (← adminPost ctx "/admin/users/disable" [("name", "root")] rid))
  check "nor remove herself"
    (last (← adminPost ctx "/admin/users/remove" [("name", "root"), ("confirm", "root")] rid))
  check "nor leave the admin group"
    (last (← adminPost ctx "/admin/users/groups" [("name", "root"),
      ("groups", toJson ["staff"])] rid))
  let some r ← ctx.store.findUserByName "root" | check "root exists" false
  checkEq "and is as she was" (r.disabled, r.groups) (false, ["admin"])
  check "the refusals are audited"
    (← audited ctx "root" "user-changed" "refused" "account root: disabling it would leave")
  check "each of them"
    ((← audited ctx "root" "user-removed" "refused" "account root: removing it") &&
      (← audited ctx "root" "user-changed" "refused" "account root: leaving admin"))
  check "she keeps her session" ((← getPage ctx "/admin" rid).status.toCode == 200)
  -- With a second administrator, each of these is allowed.
  let ann ← ctx.store.addUser "ann" ["admin"] 1
  let (aid, _) ← sessionFor ctx ann
  let d ← adminPost ctx "/admin/users/disable" [("name", "ann")] rid
  checkEq "another administrator may be disabled" d.status.toCode 200
  check "the last one is then root again"
    (last (← adminPost ctx "/admin/users/groups" [("name", "root"),
      ("groups", toJson ["staff"])] rid))
  discard <| ctx.store.setUserDisabled ann.id false 1
  let (aid2, _) ← sessionFor ctx ann
  let g ← adminPost ctx "/admin/users/groups" [("name", "root"), ("groups", toJson ["staff"])]
    rid
  checkEq "with ann enabled again, root may leave the group" g.status.toCode 200
  checkEq "and is then no administrator" (← getPage ctx "/admin" rid).status.toCode 404
  check "ann's first session ended when she was disabled"
    ((← getPage ctx "/admin" aid).status.toCode == 404)
  check "and ann is now the last"
    (last (← adminPost ctx "/admin/users/disable" [("name", "ann")] aid2))
  let back ← adminPost ctx "/admin/users/groups" [("name", "root"),
    ("groups", toJson ["admin", "staff"])] aid2
  checkEq "she may make root an administrator again" back.status.toCode 200
  let rm ← adminPost ctx "/admin/users/remove" [("name", "ann"), ("confirm", "ann")] aid2
  checkEq "and then remove herself" rm.status.toCode 200
  check "which clears her cookie"
    ((rm.headers.any fun (k, v) => k == "Set-Cookie" && containsStr v "Max-Age=0"))
  check "and she is gone" ((← ctx.store.findUserByName "ann").isNone)
  -- A user who is not an administrator is not counted, and not protected.
  discard <| ctx.store.addUser "bob" [] 1
  checkEq "a non-administrator may be disabled whatever"
    (← adminPost ctx "/admin/users/disable" [("name", "bob")] rid).status.toCode 200

/-- Accounts: what each action does, and what the audit log says. -/
def adminUserActionTests : IO Unit := withCtx fun ctx _ => do
  group "admin: accounts"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let bob ← ctx.store.addUser "bob" ["staff"] 1
  let (bid, _) ← sessionFor ctx bob
  let (bid2, _) ← sessionFor ctx bob
  discard <| ctx.store.addUser "carol" [] 1 (email := some "carol@example.org")
  -- Contact details.
  let c ← adminPost ctx "/admin/users/contact"
    [("name", "bob"), ("email", " Bob@Example.org "), ("displayName", "Bob Builder")] rid
  checkEq "the address and display name are set" c.status.toCode 200
  let some b ← ctx.store.findUserByName "bob" | check "bob" false
  checkEq "trimmed and as given" (b.email, b.displayName)
    (some "Bob@Example.org", some "Bob Builder")
  check "each change is audited with the old and the new value, by root"
    ((← audited ctx "root" "user-changed" "success"
        "account bob: email: none -> Bob@Example.org") &&
      (← audited ctx "root" "user-changed" "success"
        "account bob: display name: none -> \"Bob Builder\""))
  let bad ← adminPost ctx "/admin/users/contact" [("name", "bob"), ("email", "not-an-address")]
    rid
  checkEq "a bad address is refused" bad.status.toCode 400
  let ctl ← adminPost ctx "/admin/users/contact" [("name", "bob"),
    ("displayName", "a\u200Bb")] rid
  checkEq "so is a display name with a zero-width space" ctl.status.toCode 400
  let taken ← adminPost ctx "/admin/users/contact" [("name", "bob"),
    ("email", "CAROL@example.org")] rid
  checkEq "an address another account has, in any case, is a conflict"
    (taken.status.toCode, errorOf taken) (409, "email_taken")
  let clear ← adminPost ctx "/admin/users/contact" [("name", "bob"), ("email", ""),
    ("displayName", Json.null)] rid
  checkEq "an empty or null field clears it" clear.status.toCode 200
  checkEq "both cleared" ((← ctx.store.findUserByName "bob").map fun u => (u.email, u.displayName))
    (some (none, none))
  checkEq "nothing to change is a 400"
    (← adminPost ctx "/admin/users/contact" [("name", "bob")] rid).status.toCode 400
  checkEq "an unknown account is a 404"
    (← adminPost ctx "/admin/users/contact" [("name", "nobody"), ("email", "")] rid).status.toCode
    404
  -- Groups.
  let g ← adminPost ctx "/admin/users/groups" [("name", "bob"),
    ("groups", toJson [" ops ", "staff", "ops", ""])] rid
  checkEq "groups are replaced" g.status.toCode 200
  checkEq "trimmed, without repeats or empty ones"
    ((← ctx.store.findUserByName "bob").map (·.groups)) (some ["ops", "staff"])
  check "audited" (← audited ctx "root" "user-changed" "success"
    "account bob: groups: staff -> ops, staff")
  for bad in ["a,b", "a b", "\"x\"", "-x", "", "é"] do
    let r ← adminPost ctx "/admin/users/groups" [("name", "bob"), ("groups", toJson [bad, "ok"])]
      rid
    check s!"the group {bad} is refused, or dropped when empty"
      (if bad.isEmpty then r.status.toCode == 200 else r.status.toCode == 400)
  checkEq "groups must be a list"
    (← adminPost ctx "/admin/users/groups" [("name", "bob"), ("groups", "ops")] rid).status.toCode
    400
  -- Ending one session, then all.
  let sessions ← Session.list ctx bob.id
  checkEq "bob has two sessions" sessions.size 2
  let some first := sessions[0]? | check "a session" false
  let e ← adminPost ctx "/admin/users/sessions/end" [("name", "bob"),
    ("handle", first.handle)] rid
  checkEq "one is ended by its handle" e.status.toCode 204
  checkEq "leaving one" (← Session.list ctx bob.id).size 1
  check "audited" (← audited ctx "root" "sign-out" "success" "account bob: a session ended")
  let e2 ← adminPost ctx "/admin/users/sessions/end" [("name", "carol"),
    ("handle", ((← Session.list ctx bob.id)[0]?.map (·.handle)).getD "")] rid
  checkEq "a handle names a session of the account named, and no other" e2.status.toCode 404
  let rv ← adminPost ctx "/admin/users/revoke" [("name", "bob")] rid
  checkEq "ending all of them answers what ended" (rv.status.toCode,
    ((replyJson rv).getObjValAs? Nat "sessions").toOption) (200, some 1)
  check "both of bob's cookies are worthless"
    ((← Session.current ctx (withCookie bid)).isNone &&
      (← Session.current ctx (withCookie bid2)).isNone)
  check "audited as sessions-revoked by root"
    (← audited ctx "root" "sessions-revoked" "success" "account bob: 1 sessions")
  -- Disabling and enabling.
  let (bid3, bk) ← sessionFor ctx bob
  let d ← adminPost ctx "/admin/users/disable" [("name", "bob")] rid
  checkEq "disabling answers what ended" d.status.toCode 200
  checkEq "bob is disabled" ((← ctx.store.findUserByName "bob").map (·.disabled)) (some true)
  check "his session is gone" ((← Session.current ctx (withCookie bid3)).isNone)
  checkEq "and his passkey signs nobody in" (← signInVia (← fresh ctx) bk).status.toCode 401
  check "audited" (← audited ctx "root" "user-changed" "success" "account bob: disabled; 1 sessions")
  let en ← adminPost ctx "/admin/users/enable" [("name", "bob")] rid
  checkEq "enabling" en.status.toCode 204
  checkEq "lets the passkey in again" (← signInVia (← fresh ctx) bk).status.toCode 200
  check "audited" (← audited ctx "root" "user-changed" "success" "account bob: enabled")
  -- The user page.
  let pg ← getPage ctx "/admin/users/bob" rid
  checkEq "the account's page answers" pg.status.toCode 200
  check "and names it for the script, not as the administrator's own"
    (containsStr pg.bodyText "data-user=\"bob\"" && containsStr pg.bodyText "data-self=\"false\"")
  check "with its sessions and their end buttons"
    (containsStr pg.bodyText "data-action=\"end-session\"")
  check "and the root page says it is her own"
    (containsStr (← getPage ctx "/admin/users/root" rid).bodyText "data-self=\"true\"")
  checkEq "an unknown account's page is 404 for an administrator too"
    (← getPage ctx "/admin/users/nobody" rid).status.toCode 404
  -- Removing.
  let wrong ← adminPost ctx "/admin/users/remove" [("name", "bob"), ("confirm", "Bob")] rid
  checkEq "removal needs the name typed exactly" (wrong.status.toCode, errorOf wrong)
    (400, "confirmation_required")
  let none_ ← adminPost ctx "/admin/users/remove" [("name", "bob")] rid
  checkEq "or at all" none_.status.toCode 400
  check "bob is still there" ((← ctx.store.findUserByName "bob").isSome)
  discard <| adminPost ctx "/admin/users/contact" [("name", "bob"), ("email", "bob@x.org")] rid
  let rm ← adminPost ctx "/admin/users/remove" [("name", "bob"), ("confirm", "bob")] rid
  checkEq "with it, the account is removed" rm.status.toCode 200
  check "and gone" ((← ctx.store.findUserByName "bob").isNone)
  check "audited with its address, by root"
    (← audited ctx "root" "user-removed" "success" "account bob: removed; email: bob@x.org")
  check "and the audit log still verifies" ((← Audit.verify ctx.store) matches .ok _)

/-- Invitations: the link once, the pending list without tokens, and
withdrawing one. -/
def adminInvitationTests : IO Unit := withCtx fun ctx _ => do
  group "admin: invitations"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let r ← adminPost ctx "/admin/invitations/create" [("name", "dan"),
    ("email", "dan@example.org"), ("displayName", "Dan <D>"), ("groups", toJson ["staff"]),
    ("ttl", "2d")] rid
  checkEq "an invitation is made" r.status.toCode 201
  let url := jstr (replyJson r) "url"
  check "with a link on the issuer" (url.startsWith "https://auth.example.org/invite/")
  let token := (url.drop "https://auth.example.org/invite/".length).toString
  let now ← ctx.clock
  checkEq "expiring when asked" (((replyJson r).getObjValAs? Nat "expires").toOption)
    (some (now + 2 * 86400))
  let pending ← ctx.store.listInvitations now
  checkEq "it is pending, made by root, with its groups and contact"
    (pending.toList.map fun (_, i) => (i.userName, i.createdBy, i.groups, i.email, i.displayName))
    [("dan", "root", ["staff"], some "dan@example.org", some "Dan <D>")]
  let page ← getPage ctx "/admin/invitations" rid
  check "the list shows it" (containsStr page.bodyText "<td>dan</td>")
  check "escaped" (containsStr page.bodyText "Dan &lt;D&gt;")
  check "and never its token" (!containsStr page.bodyText token)
  let entries ← Audit.entries ctx.store
  check "nor does the audit log" (entries.all fun e => !containsStr e.detail token)
  check "which records it, by root"
    (← audited ctx "root" "invitation-issued" "success"
      "invitation for dan: groups: staff; email: dan@example.org")
  checkEq "the link works"
    ((← getPage ctx (url.drop ctx.config.issuer.length).toString).status.toCode) 200
  let taken ← adminPost ctx "/admin/invitations/create" [("name", "root")] rid
  checkEq "a taken name is a conflict" (taken.status.toCode, errorOf taken) (409, "name_taken")
  for (body, what) in ([([("name", Json.str "Not Valid")], "an invalid name"),
      ([("name", "eve"), ("ttl", "soon")], "a lifetime that is none"),
      ([("name", "eve"), ("email", "x")], "a bad address"),
      ([("name", "eve"), ("groups", toJson ["a,b"])], "a bad group"),
      ([], "no name")] : List (List (String × Json) × String)) do
    checkEq s!"{what} is refused"
      (← adminPost ctx "/admin/invitations/create" body rid).status.toCode 400
  checkEq "none of which left an invitation" (← ctx.store.listInvitations now).size 1
  let some (h, _) := pending[0]? | check "pending" false
  let w ← adminPost ctx "/admin/invitations/revoke" [("handle", Admin.invitationHandle h)] rid
  checkEq "withdrawing it" w.status.toCode 204
  checkEq "the link no longer works"
    ((← getPage ctx (url.drop ctx.config.issuer.length).toString).status.toCode) 404
  check "audited" (← audited ctx "root" "invitation-revoked" "success" "invitation for dan")
  checkEq "withdrawing it again is a 404"
    ((← adminPost ctx "/admin/invitations/revoke" [("handle", Admin.invitationHandle h)] rid).status.toCode)
    404
  checkEq "a handle that is not one is a 400"
    (← adminPost ctx "/admin/invitations/revoke" [("handle", "AAAA")] rid).status.toCode 400
  -- An invitation made here creates an account like any other.
  let r2 ← adminPost ctx "/admin/invitations/create" [("name", "eve")] rid
  let path := ((jstr (replyJson r2) "url").drop ctx.config.issuer.length).toString
  let k ← SoftKey.new
  let b ← postJson ctx (path ++ "/begin") emptyObj
  let fin ← postJson ctx (path ++ "/finish") (Json.mkObj [("credential", ← k.create (replyJson b))])
  checkEq "and its link creates the account" fin.status.toCode 201
  checkEq "with no groups" ((← ctx.store.findUserByName "eve").map (·.groups)) (some [])

/-- Clients: registering (the secret once), changing, removing. -/
def adminClientTests : IO Unit := withCtx fun ctx _ => do
  group "admin: clients"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let r ← adminPost ctx "/admin/clients/add" [("id", "wiki"), ("name", "<b>Wiki</b>"),
    ("redirectUris", toJson ["https://wiki.example.org/cb"]),
    ("postLogoutUris", toJson ["https://wiki.example.org/"]),
    ("scopes", toJson ["openid", "email"]), ("minAcr", "phr")] rid
  checkEq "a confidential client is registered" r.status.toCode 201
  let secret := jstr (replyJson r) "secret"
  check "and its secret is in the answer" (secret.length ≥ 32)
  let some c ← ctx.store.findClient "wiki" | check "wiki is stored" false
  check "which keeps only its hash" (c.secretHash == some (Oidc.tokenHash secret))
  let st := (← ctx.store.clientSettings "wiki").getD {}
  checkEq "with what was given" (c.name, c.scopes, c.redirectUris, st.postLogoutRedirectUris,
    st.minAcr, st.idTokenAlg) ("<b>Wiki</b>", ["openid", "email"],
    ["https://wiki.example.org/cb"], ["https://wiki.example.org/"], .phr, "ES256")
  let list ← getPage ctx "/admin/clients" rid
  check "the list shows it, escaped"
    (containsStr list.bodyText "&lt;b&gt;Wiki&lt;/b&gt;" && !containsStr list.bodyText "<b>Wiki")
  check "and never the secret" (!containsStr list.bodyText secret &&
    !containsStr (← getPage ctx "/admin/clients/wiki" rid).bodyText secret)
  check "nor does the audit log"
    ((← Audit.entries ctx.store).all fun e => !containsStr e.detail secret)
  check "which records it, by root" (← audited ctx "root" "client-added" "success"
    "client wiki: registered, confidential, ES256, min-acr phr")
  let again ← adminPost ctx "/admin/clients/add" [("id", "wiki"),
    ("redirectUris", toJson ["https://wiki.example.org/cb"])] rid
  checkEq "an id already registered is a conflict, not a new secret"
    (again.status.toCode, errorOf again) (409, "client_exists")
  check "the secret still authenticates"
    ((← ctx.store.findClient "wiki").bind (·.secretHash) == some (Oidc.tokenHash secret))
  let pub ← adminPost ctx "/admin/clients/add" [("id", "tv"), ("public", true),
    ("redirectUris", toJson ["http://127.0.0.1/cb"]), ("rs256", true)] rid
  checkEq "a public client" (pub.status.toCode, ((replyJson pub).getObjVal? "secret").toOption)
    (201, none)
  checkEq "with the defaults" ((← ctx.store.findClient "tv").map (·.scopes))
    (some Oidc.defaultScopes)
  checkEq "and RS256" ((← ctx.store.clientSettings "tv").map (·.idTokenAlg)) (some "RS256")
  for (body, what) in ([
      ([("id", Json.str "bad id"), ("redirectUris", toJson ["https://x.example/"])], "a bad id"),
      ([("id", "x"), ("redirectUris", toJson ["http://x.example/cb"])], "http off the loopback"),
      ([("id", "x"), ("redirectUris", toJson ([] : List String))], "no redirect URI"),
      ([("id", "x"), ("redirectUris", toJson ["https://x.example/#f"])], "a fragment"),
      ([("id", "x"), ("redirectUris", toJson ["https://x.example/"]),
        ("scopes", toJson ["profile"])], "scopes without openid"),
      ([("id", "x"), ("redirectUris", toJson ["https://x.example/"]), ("minAcr", "gold")],
        "a level that is none")] : List (List (String × Json) × String)) do
    checkEq s!"{what} is refused" (← adminPost ctx "/admin/clients/add" body rid).status.toCode 400
  check "none of which registered anything" ((← ctx.store.findClient "x").isNone)
  -- Changing.
  let u ← adminPost ctx "/admin/clients/update" [("id", "wiki"),
    ("redirectUris", toJson ["https://wiki.example.org/cb2", "https://wiki.example.org/cb"]),
    ("minAcr", "phrh"), ("name", "Wiki")] rid
  checkEq "a client is changed" u.status.toCode 204
  let some c2 ← ctx.store.findClient "wiki" | check "wiki" false
  let st2 := (← ctx.store.clientSettings "wiki").getD {}
  checkEq "what was given changes, the rest stays"
    (c2.name, c2.redirectUris, c2.scopes, st2.minAcr, st2.postLogoutRedirectUris)
    ("Wiki", ["https://wiki.example.org/cb2", "https://wiki.example.org/cb"], ["openid", "email"],
      Acr.phrh, ["https://wiki.example.org/"])
  check "and the secret stays" (c2.secretHash == c.secretHash)
  check "audited with the old and the new" (← audited ctx "root" "client-changed" "success"
    "client wiki: name: \"<b>Wiki</b>\" -> \"Wiki\"; redirect URIs: https://wiki.example.org/cb ->")
  checkEq "a bad redirect URI is refused"
    (← adminPost ctx "/admin/clients/update" [("id", "wiki"),
      ("redirectUris", toJson ["javascript:alert(1)#"])] rid).status.toCode 400
  checkEq "and changes nothing" ((← ctx.store.findClient "wiki").map (·.redirectUris))
    (some c2.redirectUris)
  checkEq "an unknown client is a 404"
    (← adminPost ctx "/admin/clients/update" [("id", "nope")] rid).status.toCode 404
  -- Removing.
  let wrong ← adminPost ctx "/admin/clients/remove" [("id", "wiki"), ("confirm", "WIKI")] rid
  checkEq "removal needs the id typed exactly" (wrong.status.toCode, errorOf wrong)
    (400, "confirmation_required")
  let rm ← adminPost ctx "/admin/clients/remove" [("id", "wiki"), ("confirm", "wiki")] rid
  checkEq "with it, the client is removed" rm.status.toCode 204
  check "and gone" ((← ctx.store.findClient "wiki").isNone)
  check "audited" (← audited ctx "root" "client-removed" "success" "client wiki: removed")

/-- Signing keys, the audit page, and what stays on the command line. -/
def adminKeyAuditTests : IO Unit := withCtx fun ctx _ => do
  group "admin: keys and the audit log"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let r ← adminPost ctx "/admin/keys/rotate" [("use", "es256")] rid
  checkEq "rotating one use" r.status.toCode 200
  let es ← ctx.store.keysOf "ES256"
  check "makes a current key and announces a next one"
    (es.size == 2 && es.any (·.state == .current) && es.any (·.state == .next))
  check "audited" (← audited ctx "root" "keys-rotated" "success" "keys es256: ")
  let all ← adminPost ctx "/admin/keys/rotate" [] rid
  checkEq "rotating all three"
    (((replyJson all).getObjValAs? (Array Json) "rotated").toOption.map (·.size)) (some 3)
  checkEq "an unknown use is refused"
    (← adminPost ctx "/admin/keys/rotate" [("use", "rsa")] rid).status.toCode 400
  let keys ← getPage ctx "/admin/keys" rid
  check "the keys page lists them" (es.all fun k => containsStr keys.bodyText k.kid)
  check "and says what stays on the command line"
    (containsStr keys.bodyText "pyle root-key \
      rotate" && containsStr keys.bodyText "pyle sessions revoke \
      --all" && containsStr keys.bodyText "command line only")
  check "with no way to do either here"
    (!(adminPosts.any fun p => containsStr p "root-key" || containsStr p "all"))
  let audit ← getPage ctx "/admin/audit" rid
  checkEq "the audit page answers" audit.status.toCode 200
  check "and says the chain is whole"
    (containsStr audit.bodyText "entries form an unbroken chain")
  check "newest first" (containsStr audit.bodyText "keys-rotated")
  for _ in [0:60] do
    let filler : Audit.Record :=
      { event := .signIn, outcome := .failure, clientAddress := "x", detail := "filler" }
    discard <| Audit.append ctx.store 1 filler
  let p1 := (← getPage ctx "/admin/audit" rid).bodyText
  let p2 := (← getPage ctx "/admin/audit?page=2" rid).bodyText
  check "fifty to a page" (containsStr p1 "Page 1 of 2" && containsStr p2 "Page 2 of 2")
  check "with links between them"
    (containsStr p1 "href=\"/admin/audit?page=2\"" && containsStr p2 "href=\"/admin/audit?page=1\"")
  check "the newest on the first" (!containsStr p1 "keys-rotated" && containsStr p2 "keys-rotated")
  checkEq "a page that is no number is the first"
    (← getPage ctx "/admin/audit?page=x" rid).status.toCode 200
  -- A broken chain is said so.
  discard <| ctx.store.run fun c =>
    Store.exec c "UPDATE audit SET detail = 'changed' WHERE seq = 2" #[]
  check "a broken chain is reported"
    (containsStr (← getPage ctx "/admin/audit" rid).bodyText "The audit log is broken")

/-- Hostile names, addresses and display names, everywhere they are shown. -/
def adminEscapeTests : IO Unit := withCtx fun ctx _ => do
  group "admin: escaping"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let evilName := "<img src=x onerror=alert(1)> \"quoted\" & 'single'"
  let evilEmail := "x\"><script>alert(1)</script>@evil.example.org"
  discard <| ctx.store.addUser "mallory" ["<g>"] 1 (email := some evilEmail)
    (displayName := some evilName)
  let s ← adminPost ctx "/admin/users/contact" [("name", "root"), ("displayName", evilName)] rid
  checkEq "a hostile display name is a display name" s.status.toCode 200
  discard <| adminPost ctx "/admin/invitations/create" [("name", "trudy"),
    ("displayName", evilName)] rid
  discard <| adminPost ctx "/admin/clients/add" [("id", "evil"), ("name", evilName),
    ("redirectUris", toJson ["https://evil.example.org/cb?a=\"<script>"])] rid
  for p in adminPages "mallory" "evil" do
    let html := (← getPage ctx p rid).bodyText
    check s!"{p} has no hostile markup"
      (!containsStr html "<img src=x" && !containsStr html "<script>alert" &&
        !containsStr html "\"quoted\"" && !containsStr html "<g>")
  let users := (← getPage ctx "/admin" rid).bodyText
  check "the accounts page shows them escaped"
    (containsStr users "&lt;img src=x onerror=alert(1)&gt; &quot;quoted&quot; &amp; &#39;single&#39;"
      && containsStr users "x&quot;&gt;&lt;script&gt;alert(1)&lt;/script&gt;@evil.example.org" &&
      containsStr users "&lt;g&gt;")
  let mine := (← getPage ctx "/admin/users/mallory" rid).bodyText
  check "and the account's page, in its fields"
    (containsStr mine "value=\"x&quot;&gt;&lt;script&gt;alert(1)&lt;/script&gt;@evil.example.org\"")
  check "the audit page escapes the details"
    (containsStr (← getPage ctx "/admin/audit" rid).bodyText "&lt;img src=x")
  check "the client page escapes its redirect URI"
    (containsStr (← getPage ctx "/admin/clients/evil" rid).bodyText
      "https://evil.example.org/cb?a=&quot;&lt;script&gt;")

/-- The rate limit on the endpoints. -/
def adminRateLimitTests : IO Unit := withCtx fun ctx _ => do
  group "admin: the rate limit"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let mut codes := #[]
  for _ in [0:8] do
    let r ← postJson ctx "/admin/users/remove" (Json.mkObj [("name", "root"), ("confirm", "x")])
      (some rid)
    codes := codes.push r.status.toCode
  check "refused requests are counted, and then held back"
    (codes.contains 400 && codes.contains 429) s!"{codes}"
  check "and audited as rate limited"
    ((← Audit.entries ctx.store).any fun e => e.event == "user-removed" &&
      e.outcome == "refused" && e.detail == "rate limited")

/-- The pages against the policy and the script, as `assetTests` does for
the others. -/
def adminPageTests : IO Unit := withCtx fun ctx _ => do
  group "admin: the pages and their script"
  let root ← ctx.store.addUser "root" ["admin"] 1
  let (rid, _) ← sessionFor ctx root
  let bob ← ctx.store.addUser "bob" [] 1
  discard <| sessionFor ctx bob
  let dis ← ctx.store.addUser "dis" [] 1
  discard <| ctx.store.setUserDisabled dis.id true 1
  discard <| adminPost ctx "/admin/clients/add" [("id", "wiki"),
    ("redirectUris", toJson ["https://wiki.example.org/cb"])] rid
  discard <| adminPost ctx "/admin/invitations/create" [("name", "dan")] rid
  let mut all := ""
  for p in adminPages "bob" "wiki" ++ ["/admin/users/root", "/admin/users/dis"] do
    let r ← getPage ctx p rid
    checkEq s!"{p} answers" r.status.toCode 200
    check s!"{p} is HTML under the strict policy"
      (r.contentType == "text/html; charset=utf-8" &&
        hasHeader r "Content-Security-Policy" contentSecurityPolicy)
    let html := r.bodyText
    check s!"{p} loads both scripts from this origin"
      (containsStr html "<script src=\"/assets/pyle.js\" defer></script>\n\
        <script src=\"/admin/assets/admin.js\" defer></script>")
    check s!"{p} has no inline script, style or handler"
      (!containsStr html "<script>" && !containsStr html " style=" &&
        !containsStr html "<style" && !containsStr html " onclick=" &&
        !containsStr html " onerror=" && !containsStr html "javascript:")
    all := all ++ html
  let script := Admin.script
  check "the script never writes HTML" (!containsStr script "innerHTML" &&
    !containsStr script "outerHTML" && !containsStr script "document.write" &&
    !containsStr script "eval(")
  let ids := (quotedAfter script " on('" ++ quotedAfter script "getElementById('" ++
    quotedAfter script "value('" ++ quotedAfter script "checked('" ++
    quotedAfter script "show('" ++ quotedAfter script "reveal('").eraseDups.filter (· != "id")
  check "the script looks up elements" (ids.length ≥ 25)
  for i in ids do
    check s!"element #{i} is on an administration page" (containsStr all s!"id=\"{i}\"")
  let actions := ((script.splitOn "data-action=\"").drop 1).map fun piece => (piece.splitOn "\"").headD ""
  for a in actions.eraseDups do
    check s!"action {a} is a button" (containsStr all s!"data-action=\"{a}\"")
  for d in ["user", "self", "client", "handle", "use", "current"] do
    check s!"data-{d} is written by a page" (containsStr all s!"data-{d}=\"")
  let posts := (quotedAfter script "adminAct('" ++ quotedAfter script "post('" ++
    quotedAfter script "getAssertion('").eraseDups
  check "the script posts to every endpoint" (adminPosts.all fun p => posts.contains p)
  for p in posts do
    check s!"POST {p} is a route" (routed .post p)
  for p in (quotedAfter script "location.assign('").eraseDups do
    check s!"GET {p} is a route" (routed .get p)
  for pg in ["admin-user", "admin-invitations", "admin-clients", "admin-client", "admin-keys"] do
    check s!"the script handles the {pg} page"
      (containsStr script s!"body.dataset.page === '{pg}'" && containsStr all s!"data-page=\"{pg}\"")
  check "and steps up at phr" (containsStr script "acr: 'phr'" &&
    containsStr script "&max_age=0&acr=phr")

/-- `adminGroup` in the configuration. -/
def adminConfigTests : IO Unit := do
  group "admin: configuration"
  let base := "{\"issuer\":\"https://a.example\",\"rpId\":\"a.example\",\
    \"origins\":[\"https://a.example\"]"
  let parse (extra : String) := (Json.parse (base ++ extra ++ "}")).toOption.map
    (Config.ofJson · "/etc/pyle")
  match parse "" with
  | some (.ok c) => checkEq "adminGroup is admin by default" c.adminGroup "admin"
  | _ => check "the minimal configuration parses" false
  match parse ",\"adminGroup\":\"ops.team\"" with
  | some (.ok c) => checkEq "and can be another group" c.adminGroup "ops.team"
  | _ => check "adminGroup parses" false
  for bad in ["\"\"", "\"a b\"", "\"a,b\"", "\"-x\"", "7", "[\"admin\"]"] do
    check s!"adminGroup {bad} is refused" (match parse s!",\"adminGroup\":{bad}" with
      | some (.error _) => true
      | _ => false)
  check "an unknown key is still refused" (match parse ",\"adminGroups\":\"admin\"" with
    | some (.error _) => true
    | _ => false)
  for (g, ok) in [("admin", true), ("Ops", true), ("a.b-c_d", true), ("9", true),
      ("", false), ("_x", false), ("a b", false), ("a,b", false), ("a\"b", false),
      (String.ofList (List.replicate 65 'a'), false)] do
    checkEq s!"the group name {(g.take 10).toString}" (Config.validGroupName g) ok
  check "the rule hides everything from a non-administrator"
    (Acr.all.all fun l => [true, false].all fun f => [true, false].all fun m =>
      Admin.rule false l f m == .hidden)
  check "sends mfa to sign in at phr" (Admin.rule true .mfa true false == .belowPhr)
  check "asks a stale phr session to step up for a change"
    (Admin.rule true .phr false true == .notFresh)
  check "lets it read" (Admin.rule true .phr false false == .allow)
  check "and lets a fresh phrh session change things" (Admin.rule true .phrh true true == .allow)

/-- The administration tests. -/
def adminTests : IO Unit := do
  adminConfigTests
  adminAccessTests
  adminOriginTests
  lastAdminTests
  adminUserActionTests
  adminInvitationTests
  adminClientTests
  adminKeyAuditTests
  adminEscapeTests
  adminRateLimitTests
  adminPageTests

end PyleTests
