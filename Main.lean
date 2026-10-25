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
    | _ =>
      IO.eprintln usage
      return 2
  catch e =>
    IO.eprintln s!"pyle: {e}"
    return 1