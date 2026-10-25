import Pyle.Http.Message

/-!
# Cookies

pyle sets one cookie, the session (DESIGN.md §4), and its attributes are fixed
here rather than chosen by each caller:

* the name has the `__Host-` prefix, which browsers only accept on a cookie
  that is `Secure`, has `Path=/` and has no `Domain` — so no subdomain can set
  or shadow it;
* `HttpOnly`, so no script reads it;
* `SameSite=Lax`, so a cross-site `POST` does not carry it.  `Lax` rather than
  `Strict` because a relying service sends the user here with a top-level
  `GET /authorize`, which must find the session.

Parsing is lenient in what it skips and strict in what it returns: a malformed
pair is ignored, never guessed at.
-/

namespace Pyle
namespace Http

/-- The session cookie's name. -/
def sessionCookieName : String := "__Host-pyle"

/-- The `name=value` pairs of a `Cookie` header, in order.  Pairs without `=`
are skipped; whitespace around names and values is trimmed; quotes are kept,
since pyle's own values never contain them. -/
def parseCookies (header : String) : List (String × String) :=
  (header.splitOn ";").filterMap fun part =>
    match part.splitOn "=" with
    | k :: v :: rest =>
      let k := k.trimAscii.toString
      if k.isEmpty then none else some (k, ("=".intercalate (v :: rest)).trimAscii.toString)
    | _ => none

/-- The value of a cookie on a request.  When a name appears more than once —
which a `__Host-` cookie cannot be made to by another site, but a buggy client
might — the first wins, as browsers send the most specific first. -/
def Req.cookie (r : Req) (name : String) : Option String :=
  let all := r.headers.filter (·.1 == "cookie") |>.flatMap (parseCookies ·.2)
  (all.find? (·.1 == name)).map (·.2)

/-- The `Set-Cookie` value that sets the session cookie for `maxAge` seconds. -/
def sessionCookie (value : String) (maxAge : Nat) : String :=
  s!"{sessionCookieName}={value}; Path=/; Secure; HttpOnly; SameSite=Lax; Max-Age={maxAge}"

/-- The `Set-Cookie` value that removes the session cookie. -/
def clearSessionCookie : String :=
  s!"{sessionCookieName}=; Path=/; Secure; HttpOnly; SameSite=Lax; Max-Age=0"

/-- Set the session cookie on a reply. -/
def Reply.setSession (r : Reply) (value : String) (maxAge : Nat) : Reply :=
  r.withHeader "Set-Cookie" (sessionCookie value maxAge)

/-- Remove the session cookie on a reply. -/
def Reply.clearSession (r : Reply) : Reply :=
  r.withHeader "Set-Cookie" clearSessionCookie

end Http
end Pyle