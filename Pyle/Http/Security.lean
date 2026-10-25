import Pyle.Http.Message

/-!
# Headers that every reply carries, and the `Origin` check

DESIGN.md §7 asks for three things of every response and request:

* **Clickjacking.**  `frame-ancestors 'none'` in a strict Content Security
  Policy.  The sign-in pages need no third-party script, inline script or
  inline style, so the policy allows none: everything comes from pyle's own
  origin, and nothing may frame it, post forms elsewhere, or change the base
  URL.
* **CSRF.**  The session cookie is `SameSite=Lax`, and every state-changing
  request must carry an `Origin` header naming one of the configured origins.
  A request without one is refused: every browser pyle supports sends it on a
  `POST`, so its absence means a client that is not a browser — and those
  authenticate by other means, on the routes that say so (`Csrf.exempt`).
* **Where requests come from.**  The client address that rate limits and the
  audit log record is the socket's peer, unless the peer is a configured
  trusted proxy, in which case `X-Forwarded-For` is read from the right, past
  every trusted hop.  Reading it from the left would let a client choose its
  own address.
-/

namespace Pyle
namespace Http

open Std.Http (Method)

/-- The Content Security Policy every reply carries. -/
def contentSecurityPolicy : String :=
  "default-src 'none'; script-src 'self'; style-src 'self'; img-src 'self' data:; " ++
  "connect-src 'self'; form-action 'self'; frame-ancestors 'none'; base-uri 'none'"

/-- The headers every reply carries. -/
def securityHeaders : List (String × String) :=
  [("Content-Security-Policy", contentSecurityPolicy),
   ("X-Content-Type-Options", "nosniff"),
   ("Referrer-Policy", "no-referrer"),
   ("X-Frame-Options", "DENY"),
   ("Cross-Origin-Opener-Policy", "same-origin"),
   ("Cross-Origin-Resource-Policy", "same-origin")]

/-- `Strict-Transport-Security`, sent when the issuer is `https://`: two years,
subdomains included, so a browser that has seen pyle once never again asks for
it over plain HTTP. -/
def strictTransportSecurity : String := "max-age=63072000; includeSubDomains"

/-- Add the security headers to a reply — with HSTS when `hsts` — and
`Cache-Control: no-store` unless the handler chose its own: a reply about who
someone is should not sit in a shared cache. -/
def withSecurityHeaders (r : Reply) (hsts : Bool := false) : Reply :=
  let hstsHeader := if hsts then [("Strict-Transport-Security", strictTransportSecurity)] else []
  let r := { r with headers := r.headers ++ securityHeaders ++ hstsHeader }
  if (r.header "cache-control").isSome then r else r.withHeader "Cache-Control" "no-store"

/-- Methods that may change state.  Everything except `GET`, `HEAD` and
`OPTIONS`, which pyle's handlers never let change anything. -/
def isStateChanging : Method → Bool
  | .get | .head | .options => false
  | _ => true

/-- Whether a request's `Origin` is one of `origins`, compared exactly.  The
literal `null` origin (sandboxed frames, some redirects) never matches. -/
def originAllowed (origins : List String) (r : Req) : Bool :=
  match r.header "origin" with
  | some o => o != "null" && origins.contains o
  | none => false

/-- The address part of a peer address, without the port.  `Std.Net` writes
IPv6 addresses bare, so the port is the part after the last `:` only for
IPv4. -/
def stripPort (peer : String) : String :=
  if peer.contains '.' then ((peer.splitOn ":").headD peer) else peer

/-- Every `X-Forwarded-For` value of a request, joined in the order they
arrived, as RFC 9110 §5.3 says repeated fields combine.  Reading only the
first would let a client put its own field after the proxy's. -/
def forwardedFor (headers : List (String × String)) : Option String :=
  match headers.filter (·.1 == "x-forwarded-for") with
  | [] => none
  | hs => some (", ".intercalate (hs.map (·.2)))

/-- The client address of a request that arrived from `peer`.  If `peer` is a
trusted proxy, the rightmost `X-Forwarded-For` entry that is not itself a
trusted proxy; otherwise `peer`.  A header with nothing usable falls back to
the peer. -/
def clientAddress (trusted : List String) (peer : String) (forwardedFor : Option String) :
    String :=
  if !trusted.contains peer then peer else
  match forwardedFor with
  | none => peer
  | some xff =>
    let hops := (xff.splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    (hops.reverse.find? (!trusted.contains ·)).getD peer

end Http
end Pyle