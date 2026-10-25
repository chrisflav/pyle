import Pyle.Http.Router
import LeanBiscuit.Util.Base64

/-!
# Sessions

A session is a row on the server and an opaque random identifier in a cookie
(DESIGN.md §4):

* the identifier is 32 random bytes, base64url without padding in the
  `__Host-pyle` cookie (`Http.sessionCookie`), and its SHA-256 in the
  database — reading the database gives nobody a session;
* a session lapses after `sessionIdleSeconds` without use and
  `sessionAbsoluteSeconds` after it began, whichever comes first;
* the identifier is rotated whenever the session's authentication changes
  (`rotate`, `reauthenticate`), so an identifier planted in a browser before
  sign-in is worthless after it;
* it records the user, the `amr` values, `auth_time` and the authenticators
  used, and a user can list theirs and end any of them.

The cookie is looked up by its hash, not compared: finding a row by the
SHA-256 of a 256-bit random value leaks nothing a timing attacker could build
on, because learning that a guessed hash is "close" to a stored one says
nothing about any identifier.

**Creating a session.**  There is exactly one function that does it,
`Session.create`, in its own section at the end of this file.  It takes the
outcome of an authentication as plain values today; in round 2 it becomes
private and is reached only through a `StrongAuthentication`, the type whose
constructors belong to the ceremony modules (§9.3).  Nothing else in pyle
inserts a session row.
-/

namespace Pyle

open Http

/-- A live session, as handlers see it. -/
structure Session where
  /-- The SHA-256 of the identifier: the row's key. -/
  idHash : Store.SecretHash
  /-- Whose session it is. -/
  user : Store.UserId
  /-- The authentication method references (RFC 8176): `hwk`, `swk`, `user`,
  `otp`, `pwd`, `mfa`. -/
  amr : List String
  /-- The authenticators used, for the session list. -/
  factors : List String
  /-- When the user last authenticated. -/
  authTime : Nat
  /-- When the session began. -/
  created : Nat
  /-- When it was last used. -/
  lastSeen : Nat
  /-- Where it was created from. -/
  clientAddress : String
  /-- The browser it was created with. -/
  userAgent : String

namespace Session

/-- The length of an identifier, in bytes. -/
def idBytes : Nat := 32

/-- base64url without padding: what the cookie carries. -/
def encodeId (b : ByteArray) : String :=
  (LeanBiscuit.Base64.encode b).replace "=" ""

/-- Read a cookie value back into an identifier.  Exactly 43 characters of the
base64url alphabet that decode to 32 bytes; anything else is not one of ours. -/
def decodeId (s : String) : Option ByteArray := do
  guard (s.length == 43 && !s.contains '=')
  let b ← LeanBiscuit.Base64.decode? s
  guard (b.size == idBytes)
  return b

/-- A public name for a session, for listing and ending it: the base64url of
its hash.  It identifies the session and cannot be used as one. -/
def handle (s : Session) : String := encodeId s.idHash.bytes

/-- A session from its row. -/
def ofRow (r : Store.SessionRow) : Session :=
  { idHash := r.idHash, user := r.user, amr := r.amr, factors := r.factors,
    authTime := r.authTime, created := r.created, lastSeen := r.lastSeen,
    clientAddress := r.clientAddress, userAgent := r.userAgent }

/-- How long the cookie should live: until the absolute timeout. -/
def cookieMaxAge (ctx : Ctx) (s : Session) (now : Nat) : Nat :=
  s.created + ctx.config.sessionAbsoluteSeconds - now

/-- The session a request's cookie names, if it is live; marks it used.  A
cookie that is malformed, unknown or past a timeout is no session. -/
def current (ctx : Ctx) (r : Req) : IO (Option Session) := do
  let some raw := r.cookie sessionCookieName | return none
  let some id := decodeId raw | return none
  let now ← ctx.clock
  let row ← ctx.store.touchSession (.of id) now ctx.config.sessionIdleSeconds
    ctx.config.sessionAbsoluteSeconds
  return row.map ofRow

/-- Give a session a new identifier.  The new identifier, to be set as the
cookie, or `none` if the session had already been rotated or ended. -/
def rotate (ctx : Ctx) (s : Session) : IO (Option (Session × String)) := do
  let id ← Crypto.randomBytes idBytes.toUSize
  let now ← ctx.clock
  let newHash := Store.SecretHash.of id
  if ← ctx.store.rotateSession s.idHash newHash now then
    return some ({ s with idHash := newHash, lastSeen := now }, encodeId id)
  return none

/-- Record a fresh authentication (a step-up) on a session, rotating its
identifier.  Like `create`, round 2 makes this reachable only with a
`StrongAuthentication`. -/
def reauthenticate (ctx : Ctx) (s : Session) (amr factors : List String) :
    IO (Option (Session × String)) := do
  let id ← Crypto.randomBytes idBytes.toUSize
  let now ← ctx.clock
  let newHash := Store.SecretHash.of id
  if ← ctx.store.reauthenticateSession s.idHash newHash amr factors now then
    return some ({ s with idHash := newHash, amr, factors, authTime := now, lastSeen := now },
      encodeId id)
  return none

/-- A user's sessions, most recently used first. -/
def list (ctx : Ctx) (user : Store.UserId) : IO (Array Session) :=
  return (← ctx.store.listSessions user).map ofRow

/-- End one of a user's sessions by its `handle`.  Whether there was one. -/
def terminate (ctx : Ctx) (user : Store.UserId) (handle : String) : IO Bool := do
  let some hash := decodeId handle | return false
  ctx.store.deleteSession user (.ofStored hash)

/-- End every session of a user; how many. -/
def terminateAll (ctx : Ctx) (user : Store.UserId) : IO Nat :=
  ctx.store.deleteUserSessions user

/-- Whether the session authenticated within the last `seconds` — the step-up
window of §4 for adding or removing authenticators and minting long-lived
tokens is five minutes. -/
def authenticatedWithin (s : Session) (now seconds : Nat) : Bool :=
  now ≤ s.authTime + seconds

/-- Set the cookie for a session on a reply. -/
def setCookie (ctx : Ctx) (s : Session) (id : String) (now : Nat) (r : Reply) : Reply :=
  r.setSession id (cookieMaxAge ctx s now)

end Session

/-! ## Creating a session

Kept apart on purpose; see the module documentation. -/

namespace Session

/-- Start a session for `user`, authenticated at the current time with `amr`
and `factors`, from the request `r`.  Returns the session and the identifier to
set as its cookie.

This is the only function that creates a session.  It checks nothing about how
the user authenticated: that is what round 2's `StrongAuthentication` argument
will carry. -/
def create (ctx : Ctx) (r : Req) (user : Store.UserId) (amr factors : List String) :
    IO (Session × String) := do
  let id ← Crypto.randomBytes idBytes.toUSize
  let now ← ctx.clock
  let row : Store.SessionRow :=
    { idHash := .of id, user, amr, factors, authTime := now, created := now,
      lastSeen := now, clientAddress := r.clientAddress,
      userAgent := ((r.header "user-agent").getD "").take 256 |>.toString }
  ctx.store.insertSession row
  return (ofRow row, encodeId id)

end Session

end Pyle