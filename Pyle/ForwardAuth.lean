import Pyle.Oidc.Client
import Pyle.Crypto.Hkdf
import Pyle.Store.Protocols
import LeanBiscuit.Token.Authorizer

/-!
# Forward authentication

For services with no sign-in of their own, pyle answers the reverse proxy's
question — Caddy's `forward_auth`, Traefik's `forwardAuth` — on every request
(DESIGN.md §5.3): `GET /forward-auth`, with the original request described in
`X-Forwarded-Method`, `-Proto`, `-Host` and `-Uri`.  Those headers are believed
only from a peer listed in `trustedProxies`; anyone else is refused.

**Who may reach what** is datalog.  Each protected host is listed in the
configuration's `forwardAuthHosts` with a policy, evaluated by `lean-biscuit`'s
authorizer over the facts `user($u)`, `group($g)` (one per group), `host($h)`,
`path($p)` and `method($m)`:

```json
"forwardAuthHosts": {
  "grafana.example.org": "allow if group(\"ops\"); allow if user(\"alice\");"
}
```

No matching `allow` is a refusal, and a host not listed is refused outright.

**The cookie.**  pyle's session cookie is a `__Host-` cookie on pyle's own
host, which no other host ever sees, so a protected host gets a cookie of its
own, `__Host-pyle-forward`.  It holds the hash of the session's identifier, the
host and an expiry, MACed with HMAC-SHA256 under a key derived from the root
key (info `"pyle forward-auth v1"`); it is not the session, and pyle checks on
every request that the session it names is still live, so signing out of pyle
ends it everywhere.  It is set in three steps:

1. a request without a good cookie is answered `302` to
   `<issuer>/forward-auth/grant?rd=<original URL>`;
2. there, with the session — after sign-in if need be — pyle checks the policy,
   issues a one-time code good for 60 seconds and bound to the session, the
   host and the path, and sends the browser to
   `https://<host>/.pyle/forward-auth?code=…`;
3. the proxy asks `/forward-auth` about that request too, and pyle answers it
   by consuming the code and replying `302` back to the original path with the
   cookie set, which the proxy hands to the browser on the protected host.

A request that is allowed is answered `200` with `Remote-User` and
`Remote-Groups` (comma-separated), and nothing else about the user.  One that
is signed in but not allowed is answered `403`; a non-`GET` request without a
cookie `401`, since a redirect would lose its body.
-/

namespace Pyle
namespace ForwardAuth

open Http
open Oidc
open LeanBiscuit LeanBiscuit.Token

/-- The cookie a protected host is given. -/
def cookieName : String := "__Host-pyle-forward"

/-- The path on a protected host that redeems a code. -/
def callbackPath : String := "/.pyle/forward-auth"

/-- How long a forward-authentication code is good for, in seconds. -/
def codeSeconds : Nat := 60

/-- The MAC key of forward-authentication cookies. -/
def macKey (rootKey : ByteArray) : ByteArray :=
  (Crypto.hkdfSha256 rootKey .empty "pyle forward-auth v1".toUTF8 32).getD .empty

/-- Eight big-endian bytes. -/
def u64 (n : Nat) : ByteArray := LeanBiscuit.Bytes.ofNatBE 8 n

/-- A cookie value naming a session for a host until `expires`. -/
def encodeCookie (key : ByteArray) (session : Store.SecretHash) (host : String)
    (expires : Nat) : String :=
  let payload := session.bytes ++ u64 expires ++ host.toUTF8
  Jose.b64urlEncode payload ++ "." ++ Jose.b64urlEncode (LeanBiscuit.Hmac.sha256 key payload)

/-- The session hash a cookie value names, if its MAC is good, it was made for
`host` and it has not expired at `now`. -/
def decodeCookie (key : ByteArray) (value host : String) (now : Nat) :
    Option Store.SecretHash := do
  let [p, m] := value.splitOn "." | none
  let payload ← Jose.b64urlDecode? p
  let mac ← Jose.b64urlDecode? m
  guard (Crypto.ctEqual mac (LeanBiscuit.Hmac.sha256 key payload))
  guard (payload.size ≥ 40)
  let expires := LeanBiscuit.Bytes.toNatBE (payload.extract 32 40)
  guard (now < expires)
  guard (payload.extract 40 payload.size == host.toUTF8)
  return .ofStored (payload.extract 0 32)

/-- A host without its port, lower-cased. -/
def hostName (authority : String) : String :=
  let a := authority.toLower
  if a.startsWith "[" then ((a.splitOn "]").headD "") ++ "]" else (a.splitOn ":").headD a

/-- The policy for a host, if it is protected. -/
def policyFor (ctx : Ctx) (host : String) : Option String :=
  (ctx.config.forwardAuthHosts.find? (·.1.toLower == host)).map (·.2)

/-- Whether a policy allows a user to make a request.  The facts are stated by
the authorizer, with no token, and the policy's own checks and policies decide;
anything but a matching `allow` is a refusal. -/
def allows (policy user : String) (groups : List String) (host path method : String) : Bool :=
  let fact (name value : String) : Builder.Fact := ⟨⟨name, [.str value]⟩⟩
  let request : AuthorizerBuilder :=
    { facts := [fact "user" user] ++ groups.map (fact "group") ++
        [fact "host" host, fact "path" path, fact "method" method] }
  match request.code policy with
  | .error _ => false
  | .ok b => (Authorizer.authorizeToken b default).toOption.isSome

/-- Split an absolute `https` URL into scheme, authority and path with query.
Plain `http` is refused: a code sent over it could be read on the way, and the
host's `__Host-` cookie could not be set there anyway. -/
def splitUrl (url : String) : Option (String × String × String) := do
  let [scheme, rest] := url.splitOn "://" | none
  guard (scheme == "https")
  let authority := ((rest.splitOn "/").headD "")
  guard (!authority.isEmpty && !authority.contains '@' && !authority.contains '?' &&
    !authority.contains '#')
  let path := (rest.drop authority.length).toString
  return (scheme, authority, if path.isEmpty then "/" else path)

/-- The path of a path with query. -/
def pathOnly (pathAndQuery : String) : String := (pathAndQuery.splitOn "?").headD pathAndQuery

/-- A `302` to `location`, the status forward-auth proxies pass on. -/
def found (location : String) : Reply :=
  { status := .found, headers := [("Location", location)] }

/-- The `Set-Cookie` value for a protected host's cookie. -/
def setCookie (value : String) (maxAge : Nat) : String :=
  s!"{cookieName}={value}; Path=/; Secure; HttpOnly; SameSite=Lax; Max-Age={maxAge}"

/-- The live session a forward-auth request carries: pyle's own cookie, when
the protected host is pyle's, or a protected host's cookie for `host`. -/
def sessionOf (ctx : Ctx) (r : Req) (host : String) : IO (Option Store.SessionRow) := do
  let now ← ctx.clock
  if let some s ← Session.current ctx r then
    return some { idHash := s.idHash, user := s.user, amr := s.amr, factors := s.factors,
                  authTime := s.authTime, created := s.created, lastSeen := s.lastSeen,
                  clientAddress := s.clientAddress, userAgent := s.userAgent }
  let some value := r.cookie cookieName | return none
  let some hash := decodeCookie (macKey ctx.rootKey) value host now | return none
  ctx.store.touchSession hash now ctx.config.sessionIdleSeconds ctx.config.sessionAbsoluteSeconds

/-- Redeem a code at the callback path: set the host's cookie and go back to
where the user was going. -/
def redeem (ctx : Ctx) (scheme authority host query : String) : IO Reply := do
  let ps := (parseUrlEncoded query).getD []
  let restart := found (issuerUrl ctx "/forward-auth/grant?" ++
    queryString [("rd", s!"{scheme}://{authority}/")])
  let some code := lookupOnce ps "code" | return restart
  let now ← ctx.clock
  let some fc ← ctx.store.consumeForwardAuthCode (tokenHash code) now | return restart
  if fc.host != host then return restart
  let live ← ctx.store.touchSession fc.session now ctx.config.sessionIdleSeconds
    ctx.config.sessionAbsoluteSeconds
  if live.isNone then return restart
  let maxAge := ctx.config.forwardAuthCookieSeconds
  return (found fc.path).withHeader "Set-Cookie"
    (setCookie (encodeCookie (macKey ctx.rootKey) fc.session host (now + maxAge)) maxAge)

/-- `GET /forward-auth`. -/
def check : Handler := fun ctx r => do
  unless ctx.config.trustedProxies.contains r.peer do
    return Reply.error .forbidden "forbidden" "forward authentication answers trusted proxies only"
  let some authority := r.header "x-forwarded-host"
    | return Reply.error .badRequest "invalid_request" "X-Forwarded-Host is required"
  let host := hostName authority
  let uri := (r.header "x-forwarded-uri").getD "/"
  let method := ((r.header "x-forwarded-method").getD "GET").toUpper
  let scheme := (r.header "x-forwarded-proto").getD "https"
  let some policy := policyFor ctx host
    | return Reply.error .forbidden "forbidden" "this host is not protected by pyle"
  let path := pathOnly uri
  if path == callbackPath then
    return ← redeem ctx scheme authority host ((uri.drop (path.length + 1)).toString)
  let some s ← sessionOf ctx r host
    | if method == "GET" || method == "HEAD" then
        return found (issuerUrl ctx "/forward-auth/grant?" ++
          queryString [("rd", s!"{scheme}://{authority}{uri}")])
      return (Reply.error .unauthorized "login_required" "sign in first").withHeader
        "WWW-Authenticate" "Cookie"
  let some user ← ctx.store.findUser s.user
    | return Reply.error .unauthorized "login_required" "sign in first"
  unless allows policy user.name user.groups host path method do
    return Reply.error .forbidden "forbidden" "the policy for this host does not allow you"
  return { status := .ok, headers :=
    [("Remote-User", user.name), ("Remote-Groups", ",".intercalate user.groups)] }

/-- `GET /forward-auth/grant?rd=<url>`: on pyle's own host, with the session,
issue a one-time code for a protected host and send the browser there to
redeem it. -/
def grant : Handler := fun ctx r => do
  let refuse (msg : String) := page "Access refused" s!"<p>{htmlEscape msg}</p>" .forbidden
  let ps := (r.queryParams.toOption).getD []
  let some rd := lookupOnce ps "rd" | return refuse "The request names no address."
  let some (scheme, authority, pathAndQuery) := splitUrl rd
    | return refuse "The address is not one pyle protects."
  let host := hostName authority
  let some policy := policyFor ctx host | return refuse "The address is not one pyle protects."
  let some s ← Session.current ctx r | return signinRedirect (Req.pathAndQuery r)
  let some user ← ctx.store.findUser s.user | return signinRedirect (Req.pathAndQuery r)
  unless allows policy user.name user.groups host (pathOnly pathAndQuery) "GET" do
    return refuse s!"Your account may not use {host}."
  let code ← randomToken
  let now ← ctx.clock
  ctx.store.addForwardAuthCode (tokenHash code)
    { session := s.idHash, host, path := pathAndQuery, expires := now + codeSeconds }
  return Reply.redirect (s!"{scheme}://{authority}{callbackPath}?" ++ queryString [("code", code)])

end ForwardAuth
end Pyle