import Pyle

/-!
# The `pyle` command

The server and its administration commands.  Every command but `version`
reads the configuration file named by `--config`, or `$PYLE_CONFIG`, or
`pyle.json` in the current directory (`Pyle.Config` describes it).

* `pyle init` creates the root key (mode 0600) and the database.
* `pyle serve` answers HTTP until it is stopped.
* `pyle user add <name> [--group <group>]…` creates an account.
* `pyle user list` lists the accounts.
* `pyle audit verify` checks the audit log's hash chain.
* `pyle client add <id> --redirect <uri>… [--public] [--scope <s>]… [--name <n>]
  [--rs256] [--post-logout <uri>]…` registers an OpenID Connect client and
  prints its secret, once.
* `pyle client list` and `pyle client remove <id>`.
* `pyle keys rotate [es256|rs256|biscuit]` promotes the waiting next key of
  each named use (all three by default) and announces a fresh one.
* `pyle keys list` lists the signing keys and their states.
-/

open Pyle

/-- What `pyle` prints when it is called wrongly. -/
def usage : String :=
  "usage: pyle <command> [--config <file>]\n\n" ++
  "commands:\n" ++
  "  init                              create the root key and the database\n" ++
  "  serve                             answer HTTP until stopped\n" ++
  "  user add <name> [--group <g>]...  create an account\n" ++
  "  user list                         list the accounts\n" ++
  "  audit verify                      check the audit log's hash chain\n" ++
  "  client add <id> --redirect <uri>... [--public] [--scope <s>]... [--name <n>]\n" ++
  "             [--rs256] [--post-logout <uri>]...\n" ++
  "                                    register an OpenID Connect client\n" ++
  "  client list                       list the clients\n" ++
  "  client remove <id>                remove a client and its tokens\n" ++
  "  keys rotate [es256|rs256|biscuit] promote the next signing key, announce a new one\n" ++
  "  keys list                         list the signing keys\n" ++
  "  version                           print the version\n\n" ++
  "The configuration file defaults to $PYLE_CONFIG, then ./pyle.json."

/-- Take every `--flag value` pair out of an argument list. -/
def takeFlag (flag : String) : List String → List String × List String
  | f :: v :: rest =>
    if f == flag then
      let (vs, others) := takeFlag flag rest
      (v :: vs, others)
    else
      let (vs, others) := takeFlag flag (v :: rest)
      (vs, f :: others)
  | [x] => ([], [x])
  | [] => ([], [])

/-- Take every occurrence of a flag without a value out of an argument list:
whether it was there, and the rest. -/
def takeSwitch (flag : String) (args : List String) : Bool × List String :=
  (args.contains flag, args.filter (· != flag))

/-- The configuration file to read. -/
def configPath (given : List String) : IO System.FilePath := do
  if let some p := given.getLast? then return p
  if let some p ← IO.getEnv "PYLE_CONFIG" then return p
  return "pyle.json"

/-- `pyle init`. -/
def init (path : System.FilePath) : IO UInt32 := do
  unless ← path.pathExists do
    IO.eprintln s!"pyle: there is no configuration file at {path}; start from this one:\n"
    IO.eprintln Config.example_
    return 1
  let config ← Config.load path
  Server.createRootKey config.rootKeyFile
  let store ← Store.Store.openAt config.database (← Http.systemClock)
  IO.println s!"pyle: wrote the root key to {config.rootKeyFile} (mode 0600)"
  IO.println s!"pyle: the database {config.database} is at schema version {← store.version}"
  IO.println "pyle: keep a copy of the root key somewhere safe; without it, sealed secrets \
    cannot be read"
  return 0

/-- Open the database a configuration names. -/
def openStore (path : System.FilePath) : IO Store.Store := do
  let config ← Config.load path
  Store.Store.openAt config.database (← Http.systemClock)

/-- `pyle user add`. -/
def userAdd (path : System.FilePath) (name : String) (groups : List String) : IO UInt32 := do
  let store ← openStore path
  let now ← Http.systemClock
  let u ← store.addUser name groups now
  discard <| Audit.append store now
    { event := .userAdded, outcome := .success, userName := some u.name, clientAddress := "cli" }
  IO.println s!"pyle: created {u.name} (id {u.id})"
  return 0

/-- `pyle user list`. -/
def userList (path : System.FilePath) : IO UInt32 := do
  let store ← openStore path
  for u in ← store.listUsers do
    let n ← store.authenticatorCount u.id
    let groups := if u.groups.isEmpty then "-" else ",".intercalate u.groups
    let state := if u.disabled then " (disabled)" else ""
    IO.println s!"{u.name}\tgroups: {groups}\tauthenticators: {n}{state}"
  return 0

/-- `pyle client add`. -/
def clientAdd (path : System.FilePath) (id : String)
    (redirects scopes names postLogout : List String) (isPublic rs256 : Bool) : IO UInt32 := do
  let store ← openStore path
  let settings : Store.ClientSettings :=
    { idTokenAlg := if rs256 then "RS256" else "ES256", postLogoutRedirectUris := postLogout }
  let secret ← Oidc.registerClient store id (names.getLast?.getD id) redirects scopes isPublic
    settings (← Http.systemClock)
  match secret with
  | some s =>
    IO.println s!"pyle: registered the confidential client {id}; its secret, shown only now:"
    IO.println s
  | none => IO.println s!"pyle: registered the public client {id} (PKCE, no secret)"
  return 0

/-- `pyle client list`. -/
def clientList (path : System.FilePath) : IO UInt32 := do
  let store ← openStore path
  for c in ← store.listClients do
    let settings := (← store.clientSettings c.id).getD {}
    let kind := if c.secretHash.isSome then "confidential" else "public"
    IO.println s!"{c.id}\t{kind}\t{settings.idTokenAlg}\tscopes: {" ".intercalate c.scopes}\t\
      redirects: {" ".intercalate c.redirectUris}"
  return 0

/-- `pyle client remove`. -/
def clientRemove (path : System.FilePath) (id : String) : IO UInt32 := do
  if ← (← openStore path).removeClient id then
    IO.println s!"pyle: removed {id} and its codes and tokens"
    return 0
  IO.eprintln s!"pyle: there is no client {id}"
  return 1

/-- `pyle keys rotate`. -/
def keysRotate (path : System.FilePath) (names : List String) : IO UInt32 := do
  let config ← Config.load path
  let store ← Store.Store.openAt config.database (← Http.systemClock)
  let rootKey ← Server.loadRootKey config.rootKeyFile
  let parse (n : String) : IO Keys.Use :=
    match Keys.Use.ofName? n with
    | some u => pure u
    | none => throw (.userError s!"'{n}' is not a key use (es256, rs256, biscuit)")
  let uses ← if names.isEmpty then pure Keys.Use.all else names.mapM parse
  for use in uses do
    let rot ← Keys.rotate store rootKey use (← Http.systemClock)
    match rot.promoted with
    | some kid => IO.println s!"pyle: {use.name}: {kid} is now current"
    | none => IO.println s!"pyle: {use.name}: no next key was waiting; the current key stays"
    IO.println s!"pyle: {use.name}: announced {rot.announced} as next"
  return 0

/-- `pyle keys list`. -/
def keysList (path : System.FilePath) : IO UInt32 := do
  let store ← openStore path
  for k in ← store.allKeys do
    let use := ((Keys.Use.ofAlgorithm? k.algorithm).map (·.name)).getD k.algorithm
    IO.println s!"{use}\t{k.state.toString}\t{k.kid}\tcreated {k.created}"
  return 0

/-- `pyle audit verify`. -/
def auditVerify (path : System.FilePath) : IO UInt32 := do
  match ← Audit.verify (← openStore path) with
  | .ok n =>
    IO.println s!"pyle: the audit log's {n} entries form an unbroken chain"
    return 0
  | .error e =>
    IO.eprintln s!"pyle: the audit log is broken: {e}"
    return 1

/-- Run a command, reporting an error as one line rather than a trace. -/
def main (args : List String) : IO UInt32 := do
  -- Everything pyle writes — the database, its journals, the root key — is
  -- for its owner only.
  Server.restrictFileModes
  let (configs, args) := takeFlag "--config" args
  let (groups, args) := takeFlag "--group" args
  let (redirects, args) := takeFlag "--redirect" args
  let (scopes, args) := takeFlag "--scope" args
  let (names, args) := takeFlag "--name" args
  let (postLogout, args) := takeFlag "--post-logout" args
  let (isPublic, args) := takeSwitch "--public" args
  let (rs256, args) := takeSwitch "--rs256" args
  try
    match args with
    | ["version"] =>
      IO.println "pyle 0.1.0"
      return 0
    | ["init"] => init (← configPath configs)
    | ["serve"] =>
      Server.run (← Config.load (← configPath configs))
      return 0
    | ["user", "add", name] => userAdd (← configPath configs) name groups
    | ["user", "list"] => userList (← configPath configs)
    | ["audit", "verify"] => auditVerify (← configPath configs)
    | ["client", "add", id] =>
      clientAdd (← configPath configs) id redirects scopes names postLogout isPublic rs256
    | ["client", "list"] => clientList (← configPath configs)
    | ["client", "remove", id] => clientRemove (← configPath configs) id
    | "keys" :: "rotate" :: uses => keysRotate (← configPath configs) uses
    | ["keys", "list"] => keysList (← configPath configs)
    | _ =>
      IO.eprintln usage
      return 2
  catch e =>
    IO.eprintln s!"pyle: {e}"
    return 1