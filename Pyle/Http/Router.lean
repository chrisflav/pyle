import Pyle.Config
import Pyle.Store.Oidc
import Pyle.Http.Cookie
import Pyle.Http.Body
import Pyle.Http.Security
import Pyle.Http.RateLimit

/-!
# Routing

A route is a method, a path pattern and a handler; the router picks the one a
request names, and does everything that must happen for *every* request in
one place, so that no handler can forget it:

1. find the route, answering `404` or `405` (with `Allow`) if there is none;
2. for a state-changing method, check `Origin` (§7), unless the route is one
   that authenticates its callers by other means and says so;
3. run the handler, turning an exception into a `500` whose body says nothing
   about why — the reason goes to the log, since it may quote SQL or stored
   values;
4. add the security headers, and HSTS when the issuer is `https://`.

An exempt route never sees the request's cookies (see `Csrf.exempt`).

Handlers are `Ctx → Req → IO Reply`, so a test builds a `Ctx` over a temporary
database and calls `dispatch` directly.  To add an endpoint, add a `Route` to
`Pyle.Server.routes`.
-/

namespace Pyle
namespace Http

open Std.Http (Method Status)

/-- What every handler is given: the configuration and the shared state. -/
structure Ctx where
  /-- The configuration. -/
  config : Config
  /-- The database. -/
  store : Store.Store
  /-- The rate limiter for endpoints that check a factor. -/
  limiter : RateLimiter
  /-- The root key (§6.3), for sealing secret columns: the one that was
  current when the request arrived. -/
  rootKey : ByteArray
  /-- For a server that should notice `pyle root-key rotate`: the fingerprint
  and the key it holds, which `Server.route` compares against the database's
  before each request and reloads when they differ.  `none` keeps `rootKey`
  as it is, as tests do. -/
  rootKeyCache : Option (IO.Ref (ByteArray × ByteArray)) := none
  /-- The current time in seconds since the Unix epoch.  A field rather than a
  call to the system clock so that tests can move time forward. -/
  clock : IO Nat

/-- Seconds since the Unix epoch, from the system clock. -/
def systemClock : IO Nat :=
  return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat

/-- A request handler. -/
abbrev Handler := Ctx → Req → IO Reply

/-- Whether a route takes part in the `Origin` check. -/
inductive Csrf where
  /-- The default: a state-changing request must carry an allowed `Origin`. -/
  | checkOrigin
  /-- For endpoints called by servers and command-line clients rather than
  browsers, which authenticate the caller themselves (the OAuth token
  endpoint, a device-code poll).  The router removes the `Cookie` header
  before such a route sees the request, so it cannot act on the session. -/
  | exempt
  deriving BEq, Repr

/-- One segment of a path pattern. -/
inductive Segment where
  /-- Must equal this text. -/
  | lit (s : String)
  /-- Matches any one non-empty segment, which the handler reads with
  `Req.param name`. -/
  | param (name : String)
  deriving BEq, Repr

/-- Parse a pattern such as `/sessions/:id`. -/
def parsePattern (p : String) : List Segment :=
  ((p.splitOn "/").filter (!·.isEmpty)).map fun s =>
    if s.startsWith ":" then .param (s.drop 1).toString else .lit s

/-- A route. -/
structure Route where
  /-- The method it answers. -/
  method : Method
  /-- The path pattern, as segments (see `Route.mk'`). -/
  pattern : List Segment
  /-- Whether it takes part in the `Origin` check. -/
  csrf : Csrf := .checkOrigin
  /-- The only spelling of the path the route answers, if it insists on one.
  Matching by segments ignores empty ones, so `/forward-auth/` and
  `//forward-auth` reach `/forward-auth`; a route that a reverse proxy must be
  able to block by path is reached by its exact path or not at all. -/
  exactPath : Option String := none
  /-- The handler. -/
  handler : Handler

/-- A route from a pattern string.  With `exact`, only the pattern itself
reaches it, spelt as it is written. -/
def Route.mk' (method : Method) (pattern : String) (handler : Handler)
    (csrf : Csrf := .checkOrigin) (exact : Bool := false) : Route :=
  { method, pattern := parsePattern pattern, csrf, handler,
    exactPath := if exact then some pattern else none }

/-- The segments of a path.  `none` if the path is not absolute, or names `.`
or `..` in any spelling, which no route uses and which only path confusion
wants. -/
def pathSegments (path : String) : Option (List String) := do
  guard (path.startsWith "/")
  let segs := (path.splitOn "/").filter (!·.isEmpty)
  guard (segs.all fun s =>
    let l := s.toLower.replace "%2e" "."
    l != "." && l != "..")
  return segs

/-- Match segments against a pattern, giving the parameters. -/
def matchPattern : List Segment → List String → Option (List (String × String))
  | [], [] => some []
  | .lit l :: ps, s :: ss => if l == s then matchPattern ps ss else none
  | .param n :: ps, s :: ss => return (n, s) :: (← matchPattern ps ss)
  | _, _ => none

/-- The upper-case name of a method, for `Allow`. -/
def methodName (m : Method) : String := toString m

/-- Answer one request with the first route that matches it. -/
def dispatch (routes : List Route) (ctx : Ctx) (r : Req) : IO Reply := do
  let reply ← go
  return withSecurityHeaders reply (hsts := ctx.config.issuer.startsWith "https://")
where
  /-- Everything but the headers. -/
  go : IO Reply := do
    let some segs := pathSegments r.path
      | return Reply.error .notFound "not_found"
    let matching := routes.filterMap fun rt =>
      if rt.exactPath.all (· == r.path) then (rt, ·) <$> matchPattern rt.pattern segs
      else none
    if matching.isEmpty then return Reply.error .notFound "not_found"
    let some (rt, params) := matching.find? (·.1.method == r.method)
      | let allow := ", ".intercalate (matching.map (methodName ·.1.method)).eraseDups
        return (Reply.error .methodNotAllowed "method_not_allowed").withHeader "Allow" allow
    if isStateChanging r.method && rt.csrf == .checkOrigin &&
        !originAllowed ctx.config.origins r then
      return Reply.error .forbidden "forbidden" "cross-origin request refused"
    -- An exempt route is reached without the Origin check, so it must not
    -- be able to act on the session: it does not get to see the cookie.
    let headers := if rt.csrf == .exempt then r.headers.filter (·.1 != "cookie") else r.headers
    try rt.handler ctx { r with params, headers }
    catch e =>
      IO.eprintln s!"pyle: {methodName r.method} {r.path}: {e}"
      return Reply.error .internalServerError "server_error"

end Http
end Pyle