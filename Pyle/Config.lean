import Lean.Data.Json
import LeanBiscuit.Parser
import Pyle.Session.Acr

/-!
# Configuration

One JSON file, read at startup by every command:

```json
{
  "issuer": "https://auth.example.org",
  "host": "127.0.0.1",
  "port": 8420,
  "database": "pyle.db",
  "rootKeyFile": "root.key",
  "rpId": "auth.example.org",
  "origins": ["https://auth.example.org"],
  "sessionIdleSeconds": 28800,
  "sessionAbsoluteSeconds": 2592000,
  "trustedProxies": ["127.0.0.1"],
  "allowPasswords": false,
  "attestationRoots": [],
  "aaguidAllowList": [],
  "adminGroup": "admin"
}
```

Only `issuer`, `rpId` and `origins` are required; the rest have the defaults
shown, and the protocol settings (`accessTokenSeconds`, `forwardAuthHosts` and
the others in their block below) have the defaults their fields give.
`aaguidAllowList` needs `attestationRoots`, since an AAGUID is only worth
checking in an attestation whose chain is verified.  Relative paths are
relative to the directory the configuration file is in, so a deployment
directory can be moved as a whole.

An unknown key is an error rather than ignored.  A misspelt
`sessionIdleSecond` silently falling back to eight hours is the kind of
mistake nobody notices until it matters.
-/

namespace Pyle

open Lean (Json)

/-- Everything pyle reads at startup. -/
structure Config where
  /-- The issuer URL: `iss` in every token, and the base of every URL pyle
  hands out.  `https://`, no trailing slash. -/
  issuer : String
  /-- The address to listen on.  The loopback by default, because TLS is
  terminated by a reverse proxy in front (§6.1). -/
  host : String := "127.0.0.1"
  /-- The port to listen on.  Zero picks a free one, which only the tests want. -/
  port : UInt16 := 8420
  /-- The SQLite database file. -/
  database : System.FilePath := "pyle.db"
  /-- The file holding the 32-byte root key (§6.3). -/
  rootKeyFile : System.FilePath := "root.key"
  /-- The WebAuthn relying-party id: the registrable domain credentials are
  bound to. -/
  rpId : String
  /-- The exact origins WebAuthn responses and state-changing requests may
  come from. -/
  origins : List String
  /-- How long a session may go unused, in seconds (§4: eight hours). -/
  sessionIdleSeconds : Nat := 8 * 3600
  /-- How long a session may live at all, in seconds (§4: thirty days). -/
  sessionAbsoluteSeconds : Nat := 30 * 86400
  /-- Peer addresses whose `X-Forwarded-For` is believed.  Empty by default:
  then the client address is the socket's peer, and a header anyone can send
  decides nothing. -/
  trustedProxies : List String := []
  -- Sign-in (DESIGN §1–§4).
  /-- Whether a user may set a password as one of their factors.  Off by
  default (§1): a password is never alone sufficient, and most deployments
  have no device without a platform authenticator. -/
  allowPasswords : Bool := false
  /-- Files holding the trust anchors for `packed` full attestation, each in
  DER or PEM.  Empty by default: then an attestation chain is not validated
  and counts for nothing. -/
  attestationRoots : List System.FilePath := []
  /-- The authenticator models (AAGUIDs, as hex with or without hyphens) that
  may be registered.  Empty by default, meaning any.  When it is set, a
  registration must carry `packed` full attestation whose chain ends in one of
  `attestationRoots` and whose AAGUID is listed; without a verified chain the
  AAGUID is only the authenticator's word. -/
  aaguidAllowList : List String := []
  -- Protocols (DESIGN.md §5): token lifetimes, the device grant, and the hosts
  -- forward authentication answers for.
  /-- How long an access token (a biscuit) is good for, in seconds. -/
  accessTokenSeconds : Nat := 3600
  /-- How long an ID token is good for, in seconds. -/
  idTokenSeconds : Nat := 600
  /-- How long a refresh token is good for after it is issued, in seconds. -/
  refreshTokenSeconds : Nat := 30 * 86400
  /-- How long a device code waits for the user, in seconds (RFC 8628 §3.2). -/
  deviceCodeSeconds : Nat := 600
  /-- The least seconds between two polls with a device code. -/
  devicePollSeconds : Nat := 5
  /-- How long a kleis attestation block is good for, in seconds (§5.4). -/
  attestationSeconds : Nat := 300
  /-- The lowest level a sign-in must reach for pyle to attest it to kleis
  (§5.4): `mfa` unless configured.  A kleis grant that trusts pyle's `user`
  facts trusts them at this level. -/
  kleisMinAcr : Acr := .mfa
  /-- The hosts forward authentication answers for, each with the datalog
  policy deciding who may reach it (§5.3).  A host not listed is refused. -/
  forwardAuthHosts : List (String × String) := []
  /-- The lowest level a session must reach for a protected host, for the
  hosts configured with one (`minAcr`); every other protected host has the
  floor, `mfa`. -/
  forwardAuthMinAcr : List (String × Acr) := []
  /-- How long the forward-authentication cookie a protected host is given
  lives, in seconds; the session behind it is checked on every request. -/
  forwardAuthCookieSeconds : Nat := 8 * 3600
  /-- A secret the proxy must send in `X-Pyle-Forward-Auth` for `/forward-auth`
  to answer, compared in constant time.  Required as soon as
  `forwardAuthHosts` names a host: a proxy rule that keeps `/forward-auth`
  off the public virtual host is one spelling of the path away from not
  doing so, and without the secret anyone who reaches it can ask pyle about
  any session cookie they hold. -/
  forwardAuthSecret : Option String := none
  -- Administration (the pages under `/admin`).
  /-- The group whose enabled members may use the administration pages, from
  a session at `phr` or better.  `admin` unless configured; a group name
  (`Config.validGroupName`). -/
  adminGroup : String := "admin"
  deriving Repr, Inhabited

namespace Config

/-- Whether a group name is acceptable: 1 to 64 characters from ASCII letters,
digits, `-`, `_` and `.`, starting with a letter or digit.  Groups appear in
`Remote-Groups` (joined with commas), in datalog facts and in tokens, and a
narrow alphabet keeps every one of those encodings trivial. -/
def validGroupName (g : String) : Bool :=
  let cs := g.toList
  !cs.isEmpty && cs.length ≤ 64 &&
    cs.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') &&
    (cs.head?.any Char.isAlphanum)

/-- The keys a configuration file may contain. -/
def knownKeys : List String :=
  ["issuer", "host", "port", "database", "rootKeyFile", "rpId", "origins",
   "sessionIdleSeconds", "sessionAbsoluteSeconds", "trustedProxies",
   "allowPasswords", "attestationRoots", "aaguidAllowList",
   "accessTokenSeconds", "idTokenSeconds", "refreshTokenSeconds", "deviceCodeSeconds",
   "devicePollSeconds", "attestationSeconds", "kleisMinAcr", "forwardAuthHosts",
   "forwardAuthCookieSeconds", "forwardAuthSecret", "adminGroup"]

/-- A required string field. -/
private def reqStr (j : Json) (k : String) : Except String String :=
  match j.getObjVal? k with
  | .ok (.str s) => .ok s
  | .ok _ => .error s!"'{k}' must be a string"
  | .error _ => .error s!"'{k}' is required"

/-- An optional field, read with `f` when present. -/
private def opt (j : Json) (k : String) (dflt : α) (f : Json → Option α) (what : String) :
    Except String α :=
  match j.getObjVal? k with
  | .error _ => .ok dflt
  | .ok v => match f v with
    | some a => .ok a
    | none => .error s!"'{k}' must be {what}"

/-- A JSON string. -/
private def asStr : Json → Option String
  | .str s => some s
  | _ => none

/-- A JSON non-negative integer. -/
private def asNat (v : Json) : Option Nat := (v.getNat?).toOption

/-- A JSON boolean. -/
private def asBool : Json → Option Bool
  | .bool b => some b
  | _ => none

/-- An AAGUID as written in the configuration: 32 hexadecimal digits, with or
without the hyphens of the UUID form, in either case.  The normalised form is
lower-case hex without hyphens. -/
def normaliseAaguid (s : String) : Option String :=
  let cs := s.toList.filter (· != '-') |>.map Char.toLower
  if cs.length == 32 && cs.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    some (String.ofList cs)
  else none

/-- A JSON array of strings. -/
private def asStrs : Json → Option (List String)
  | .arr xs => xs.toList.mapM asStr
  | _ => none

/-- A protected host's entry in `forwardAuthHosts`: its policy as a string,
or an object `{"policy": …, "minAcr": …}` whose `minAcr` is a level's short
name or identifier (`Acr.ofIdentifier?`).  The policy, and the minimum if one is
given. -/
def forwardHost (host : String) : Json → Except String (String × Option Acr)
  | .str policy => .ok (policy, none)
  | v@(.obj kvs) => do
    for (k, _) in kvs.toArray do
      unless k == "policy" || k == "minAcr" do
        throw s!"'{k}' is not a key of a forward-auth host ('{host}')"
    let some policy := (v.getObjValAs? String "policy").toOption
      | throw s!"the forward-auth host '{host}' needs a 'policy' string"
    match v.getObjVal? "minAcr" with
    | .error _ => return (policy, none)
    | .ok m =>
      let some a := (asStr m).bind Acr.ofIdentifier?
        | throw s!"the 'minAcr' of '{host}' is not a level (mfa, phr or phrh)"
      return (policy, some a)
  | _ => .error s!"the forward-auth host '{host}' must be a policy or an object with one"

/-- Split an `https://host[:port][/path]` URL into scheme, authority and path,
if it is one pyle accepts as an issuer or origin: `https` with a non-empty
host, or `http` only when the host is exactly `localhost` or `127.0.0.1` (for
development).  The host is compared whole, so `http://localhost.evil.example`
is refused.  No userinfo, query, fragment, or trailing `/`. -/
def parseUrlBase (url : String) : Option (String × String × String) := do
  let (scheme, rest) ← match url.splitOn "://" with
    | [scheme, rest] => some (scheme, rest)
    | _ => none
  let (authority, path) := match rest.splitOn "/" with
    | a :: segs => (a, if segs.isEmpty then "" else "/" ++ "/".intercalate segs)
    | [] => ("", "")
  guard (!authority.isEmpty && !url.contains '?' && !url.contains '#' &&
    !authority.contains '@' && !url.endsWith "/")
  let host := match authority.splitOn ":" with
    | [h, p] => if !p.isEmpty && p.all Char.isDigit then some h else none
    | [h] => some h
    | _ => none
  let host ← host
  guard (!host.isEmpty)
  guard (scheme == "https" || (scheme == "http" && (host == "localhost" || host == "127.0.0.1")))
  return (scheme, authority, path)

/-- Read a configuration from its JSON, resolving relative paths against
`base`.  Checks what can be checked without the network: the issuer is
`https://` (or `http://localhost` for development), the origins are origins,
and the timeouts are positive with the idle one no longer than the absolute
one. -/
def ofJson (j : Json) (base : System.FilePath := ".") : Except String Config := do
  let .obj kvs := j | throw "the configuration must be a JSON object"
  for (k, _) in kvs.toArray do
    unless knownKeys.contains k do throw s!"unknown configuration key '{k}'"
  let issuer ← reqStr j "issuer"
  unless (parseUrlBase issuer).isSome do
    throw "'issuer' must be an https:// URL with no query or fragment and no trailing '/' \
      (http:// only for localhost or 127.0.0.1)"
  let rpId ← reqStr j "rpId"
  if rpId.isEmpty then throw "'rpId' must not be empty"
  let origins ← match j.getObjVal? "origins" with
    | .ok v => match asStrs v with
      | some os => pure os
      | none => throw "'origins' must be an array of strings"
    | .error _ => throw "'origins' is required"
  if origins.isEmpty then throw "'origins' must name at least one origin"
  for o in origins do
    match parseUrlBase o with
    | some (_, _, "") => pure ()
    | _ => throw s!"'{o}' is not an origin (scheme://host[:port], no path; \
        http:// only for localhost or 127.0.0.1)"
  let host ← opt j "host" "127.0.0.1" asStr "a string"
  let port ← opt j "port" 8420 asNat "a port number"
  if port ≥ 65536 then throw "'port' must be below 65536"
  let database ← opt j "database" "pyle.db" asStr "a path"
  let rootKeyFile ← opt j "rootKeyFile" "root.key" asStr "a path"
  let idle ← opt j "sessionIdleSeconds" (8 * 3600) asNat "a number of seconds"
  let absolute ← opt j "sessionAbsoluteSeconds" (30 * 86400) asNat "a number of seconds"
  if idle == 0 || absolute == 0 then throw "session timeouts must be positive"
  if idle > absolute then
    throw "'sessionIdleSeconds' must not exceed 'sessionAbsoluteSeconds'"
  let trustedProxies ← opt j "trustedProxies" [] asStrs "an array of addresses"
  let allowPasswords ← opt j "allowPasswords" false asBool "true or false"
  let attestationRoots ← opt j "attestationRoots" [] asStrs "an array of paths"
  let aaguids ← opt j "aaguidAllowList" [] asStrs "an array of AAGUIDs"
  let aaguidAllowList ← aaguids.mapM fun a => match normaliseAaguid a with
    | some n => pure n
    | none => throw s!"'{a}' is not an AAGUID (32 hexadecimal digits)"
  if !aaguidAllowList.isEmpty && attestationRoots.isEmpty then
    throw "'aaguidAllowList' needs 'attestationRoots': without them no AAGUID can be trusted"
  let positive (k : String) (dflt : Nat) : Except String Nat := do
    let n ← opt j k dflt asNat "a number of seconds"
    if n == 0 then throw s!"'{k}' must be positive"
    return n
  let accessTokenSeconds ← positive "accessTokenSeconds" 3600
  let idTokenSeconds ← positive "idTokenSeconds" 600
  let refreshTokenSeconds ← positive "refreshTokenSeconds" (30 * 86400)
  let deviceCodeSeconds ← positive "deviceCodeSeconds" 600
  let devicePollSeconds ← positive "devicePollSeconds" 5
  let attestationSeconds ← positive "attestationSeconds" 300
  let kleisMinAcr ← opt j "kleisMinAcr" Acr.mfa (fun v => (asStr v).bind Acr.ofIdentifier?)
    "a level (mfa, phr or phrh)"
  let forwardAuthCookieSeconds ← positive "forwardAuthCookieSeconds" (8 * 3600)
  let hostEntries ← match j.getObjVal? "forwardAuthHosts" with
    | .error _ => pure []
    | .ok (.obj kvs) => kvs.toArray.toList.mapM fun (k, v) => do
      return (k, ← forwardHost k v)
    | .ok _ => throw "'forwardAuthHosts' must be an object from host names to datalog policies"
  let forwardAuthHosts := hostEntries.map fun (h, p, _) => (h, p)
  let forwardAuthMinAcr := hostEntries.filterMap fun (h, _, m) => m.map (h, ·)
  let forwardAuthSecret ← opt j "forwardAuthSecret" none (fun v => (asStr v).map some)
    "a string"
  if forwardAuthSecret.any (·.length < 16) then
    throw "'forwardAuthSecret' must be at least 16 characters"
  if !forwardAuthHosts.isEmpty && forwardAuthSecret.isNone then
    throw "'forwardAuthHosts' needs 'forwardAuthSecret', the secret the proxy sends in \
      X-Pyle-Forward-Auth"
  for (host, policy) in forwardAuthHosts do
    if host.isEmpty || host.contains '/' || host.contains '@' then
      throw s!"'{host}' in 'forwardAuthHosts' is not a host name"
    match LeanBiscuit.Parser.parseAuthorizer policy with
    | .ok src =>
      if src.policies.isEmpty then
        throw s!"the forward-auth policy for '{host}' has no allow or deny policy"
    | .error e => throw s!"the forward-auth policy for '{host}' is not datalog: {e}"
  let adminGroup ← opt j "adminGroup" "admin" asStr "a string"
  unless validGroupName adminGroup do
    throw "'adminGroup' must be a group name (letters, digits, '-', '_' and '.', at most 64, \
      starting with a letter or digit)"
  let resolve (p : String) : System.FilePath :=
    let fp : System.FilePath := p
    if fp.isAbsolute then fp else base / fp
  return { issuer, host, port := port.toUInt16, database := resolve database,
           rootKeyFile := resolve rootKeyFile, rpId, origins,
           sessionIdleSeconds := idle, sessionAbsoluteSeconds := absolute, trustedProxies,
           allowPasswords, attestationRoots := attestationRoots.map resolve, aaguidAllowList,
           accessTokenSeconds, idTokenSeconds, refreshTokenSeconds, deviceCodeSeconds,
           devicePollSeconds, attestationSeconds, kleisMinAcr, forwardAuthHosts, forwardAuthMinAcr,
           forwardAuthCookieSeconds, forwardAuthSecret, adminGroup }

/-- Read and check a configuration file. -/
def load (path : System.FilePath) : IO Config := do
  let text ← try IO.FS.readFile path
    catch e => throw (.userError s!"cannot read the configuration file {path}: {e}")
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw (.userError s!"{path} is not JSON: {e}")
  let base := path.parent.getD "."
  let base : System.FilePath := if base.toString.isEmpty then "." else base
  match ofJson j base with
  | .ok c => return c
  | .error e => throw (.userError s!"{path}: {e}")

/-- A starting configuration, printed by `pyle init` when there is none. -/
def example_ : String :=
  "{\n" ++
  "  \"issuer\": \"https://auth.example.org\",\n" ++
  "  \"rpId\": \"auth.example.org\",\n" ++
  "  \"origins\": [\"https://auth.example.org\"],\n" ++
  "  \"database\": \"pyle.db\",\n" ++
  "  \"rootKeyFile\": \"root.key\"\n" ++
  "}"

end Config
end Pyle