import Std.Http
import Std.Net
import Pyle.Session.Session
import Pyle.SignIn.Routes
import Pyle.Audit
import Pyle.Sys
import Pyle.Oidc.Routes
import Pyle.RootKey

/-!
# The server

`pyle serve` answers HTTP on one port, behind a reverse proxy that terminates
TLS (DESIGN.md §6.1).  This module holds the route table, the `Std.Http`
adapter, and the start-up that opens the database and reads the root key.

Routing is a function from a `Req` to a `Reply` (`route`), so that the suite
can drive every endpoint without a socket; `serve` adapts `Std.Http` to it and
back, and is the only code here that touches the network.

**Adding an endpoint.**  Write a `Http.Handler` and add a `Route.mk'` line to
`routes`.  The router takes care of `404`/`405`, the `Origin` check, the
security headers and turning exceptions into `500`s; the handler does the rest.
A route that is called by servers rather than browsers, and authenticates them
itself, passes `(csrf := .exempt)`.

The endpoints so far:

* `GET /healthz` — `200` with `{"status":"ok"}` once the database answers.
* `POST /logout` — ends the request's session, if any, and clears the cookie.
* `SignIn.routes` — the sign-in, account and invitation pages and their
  endpoints (`Pyle.SignIn.Routes`).
* the protocols of DESIGN.md §5, listed in `Pyle.Oidc.Routes`.
-/

namespace Pyle
namespace Server

open Http
open Lean (Json)
open Std.Net
open Std.Async
open Std.Http (Request Response Body Header Status Method)
open Std.Http.Server (Handler)

/-! ## Endpoints -/

/-- `GET /healthz`: whether the database answers. -/
def healthz : Http.Handler := fun ctx _ => do
  let v ← ctx.store.version
  if v == Store.schemaVersion then
    return .json (Json.mkObj [("status", "ok")])
  return .error .serviceUnavailable "unavailable" "the database is not at the expected version"

/-- `POST /logout`: end the request's session and clear the cookie.  Answers
the same whether or not there was a session. -/
def logout : Http.Handler := fun ctx r => do
  if let some s ← Session.current ctx r then
    discard <| ctx.store.deleteSession s.user s.idHash
    let name := (← ctx.store.findUser s.user).map (·.name)
    Audit.log ctx r .signOut .success (userName := name)
  return Reply.noContent.clearSession

/-- Every route. -/
def routes : List Route := [
  .mk' .get "/healthz" healthz,
  .mk' .post "/logout" logout
] ++ SignIn.routes ++ Oidc.routes

/-- The context with the root key the database is sealed under now.  A
context with a `rootKeyCache` compares the fingerprint it holds with the
database's — one indexed read — and, when `pyle root-key rotate` has replaced
the key since, reads the new one (`RootKey.resolve`, which also finishes a
rotation that stopped before installing its key) and keeps it for the
requests after.  It does not wait for the root key's lock: while a rotation
holds it, the pending key is used as it is and the rotation installs it. -/
def withCurrentRootKey (ctx : Ctx) : IO Ctx := do
  let some cache := ctx.rootKeyCache | return ctx
  let (held, key) ← cache.get
  match ← ctx.store.recordedRootKey with
  | some recorded =>
    if recorded == held then return { ctx with rootKey := key }
    let key ← RootKey.resolve ctx.store ctx.config.rootKeyFile (← ctx.clock)
      (locking := .tryOnly)
    cache.set (Store.rootKeyId key, key)
    IO.eprintln s!"pyle: the root key was replaced; now using {RootKey.showId recorded}"
    return { ctx with rootKey := key }
  | none => return { ctx with rootKey := key }

/-- Answer one request, under the current root key.  A root key that cannot
be read any more is a `503` until it can. -/
def route (ctx : Ctx) (r : Req) : IO Reply := do
  let ctx ← try withCurrentRootKey ctx
    catch e =>
      IO.eprintln s!"pyle: the root key: {e}"
      return withSecurityHeaders (hsts := ctx.config.issuer.startsWith "https://") <|
        Reply.error .serviceUnavailable "unavailable" "the server cannot read its root key"
  dispatch routes ctx r

/-! ## Start-up -/

/-- The length of the root key, in bytes. -/
def rootKeyBytes : Nat := RootKey.bytes

/-- Write a new random root key to `path`, readable only by its owner
(`RootKey.create`). -/
def createRootKey (path : System.FilePath) : IO Unit := RootKey.create path

/-- Make every file the process creates from now on private to its owner
(`umask 077`): the database and the journal files SQLite creates beside it. -/
def restrictFileModes : IO Unit := discard <| Sys.umask 0o077

/-- Read a root key file, checking its length (`RootKey.load`). -/
def loadRootKey (path : System.FilePath) : IO ByteArray := RootKey.load path

/-- Open the database (migrating it) and the root key it is sealed under
(`RootKey.resolve`): everything a handler needs.  Without a key file there is
nothing to open, and no database is created. -/
def openCtx (config : Config) (clock : IO Nat := systemClock) : IO Ctx := do
  restrictFileModes
  unless (← config.rootKeyFile.pathExists) ||
      !(← RootKey.pendingFiles config.rootKeyFile).isEmpty do
    discard <| RootKey.load config.rootKeyFile
  let store ← Store.Store.openAt config.database (← clock)
  let rootKey ← RootKey.resolve store config.rootKeyFile (← clock)
  return { config, store, limiter := ← RateLimiter.new, rootKey, clock,
           rootKeyCache := some (← IO.mkRef (Store.rootKeyId rootKey, rootKey)) }

/-! ## The `Std.Http` adapter -/

/-- The largest request body accepted.  pyle's largest legitimate request is a
WebAuthn registration response, a few kilobytes. -/
def maxBodyBytes : UInt64 := 65536

/-- The address of a socket peer, without the port. -/
def peerAddress : SocketAddress → String
  | .v4 a => toString a.addr
  | .v6 a => toString a.addr

/-- The handler state `Std.Http` is given. -/
structure Adapter where
  /-- What handlers are given. -/
  ctx : Ctx

/-- A reply as a `Std.Http` response.  A header `Std.Http` would refuse (a
value with a line break, say) is dropped and logged rather than allowed to
crash the connection; pyle's own headers never are. -/
def toResponse (rep : Reply) : Async (Response Body.Any) := do
  let headers := (if rep.contentType.isEmpty then [] else [("Content-Type", rep.contentType)])
    ++ rep.headers
  let mut b := Response.withStatus rep.status
  for (k, v) in headers do
    match b.header? k v with
    | some b' => b := b'
    | none => IO.eprintln s!"pyle: dropped an invalid response header '{k}'"
  b.fromBytes rep.body

/-- A `Std.Http` request as a `Req`. -/
def toReq (config : Config) (req : Request Body.Stream) (body : ByteArray) : Req :=
  let target := toString req.line.uri
  let (path, query) := match target.splitOn "?" with
    | [] => ("/", "")
    | p :: rest => (p, "?".intercalate rest)
  let headers := req.line.headers.toList.map fun (k, v) => (toString k |>.toLower, toString v)
  let peer := match req.extensions.get Std.Http.Server.RemoteAddr with
    | some a => peerAddress a.addr
    | none => ""
  let xff := forwardedFor headers
  { method := req.line.method, path, query, headers, body, peer,
    clientAddress := Http.clientAddress config.trustedProxies peer xff }

instance : Handler Adapter where
  onRequest a req := do
    let body : ByteArray ← if isStateChanging req.line.method then
        req.body.readAll (maximumSize := some maxBodyBytes)
      else pure .empty
    toResponse (← route a.ctx (toReq a.ctx.config req body))
  onFailure _ e := IO.eprintln s!"pyle: connection: {e}"

/-- The `Std.Http` limits. -/
def httpConfig : Std.Http.Config where
  maxBodySize := maxBodyBytes.toNat
  maxUriLength := 4096

/-- Start serving on the configured address.  Returns the port actually bound
(the configured one, unless it was zero) and an action that stops the server. -/
def serve (ctx : Ctx) : IO (UInt16 × IO Unit) := do
  let some hostAddr := IPv4Addr.ofString ctx.config.host
    | throw (.userError s!"'{ctx.config.host}' is not an IPv4 address")
  let server ← Async.block do
    Std.Http.Server.serve (SocketAddress.v4 { addr := hostAddr, port := ctx.config.port })
      (Adapter.mk ctx) httpConfig
  let port := match server.localAddr with
    | some (.v4 a) => a.port
    | some (.v6 a) => a.port
    | none => ctx.config.port
  return (port, Async.block server.shutdownAndWait)

/-- Remove what has expired: sessions past a timeout, challenges and device
codes past their expiry.  Nothing depends on this for correctness — every
lookup checks expiry itself — it only keeps the tables small. -/
def purge (ctx : Ctx) : IO Unit := do
  let now ← ctx.clock
  discard <| ctx.store.purgeSessions now ctx.config.sessionIdleSeconds
    ctx.config.sessionAbsoluteSeconds
  discard <| ctx.store.purgeChallenges now
  discard <| ctx.store.purgeDeviceCodes now
  discard <| ctx.store.purgeCodes now
  discard <| ctx.store.purgeForwardAuthCodes now

/-- Serve until the process is stopped. -/
def run (config : Config) : IO Unit := do
  let ctx ← openCtx config
  let (port, _) ← serve ctx
  IO.println s!"pyle: listening on {config.host}:{port} as {config.issuer}"
  (← IO.getStdout).flush
  -- The server runs on its own tasks; this one only purges, once an hour.
  while true do
    try purge ctx
    catch e => IO.eprintln s!"pyle: purge: {e}"
    IO.sleep 3600000

end Server
end Pyle