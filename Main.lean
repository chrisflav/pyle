import Pyle

/-!
# The `pyle` command

The server and its administration commands.  Every command but `version`
reads the configuration file named by `--config`, or `$PYLE_CONFIG`, or
`pyle.json` in the current directory (`Pyle.Config` describes it).

* `pyle init` creates the root key (mode 0600) and the database.
* `pyle serve` answers HTTP until it is stopped.
* `pyle user add <name> [--group <group>]… [--email <e>] [--display-name <n>]`
  creates an account.
* `pyle user set <name> [--email <e> | --no-email] [--display-name <n> |
  --no-display-name]` sets or clears an account's email address and display
  name, in one transaction, auditing the old and new values.  Only an
  administrator sets these, never the user, which is why the `email` claim is
  stated as verified.  Services such as Zulip key accounts by address: an
  address freed here and given to another account hands that account
  whatever the old one had there.
* `pyle user list` lists the accounts.
* `pyle user disable <name>` disables an account and ends its access as
  `sessions revoke --user` does; `pyle user enable <name>` enables it again.
  A disabled account cannot sign in by any method, its sessions and refresh
  tokens are gone, and `/userinfo` refuses its access tokens.
* `pyle user remove <name> --yes` deletes an account and everything that is
  its, and the pending invitations for its name or address, recording its
  name and email address in the audit log.  The name and the address are
  then free for another account, which services keying accounts by them take
  for the removed one.
* `pyle sessions list [--user <name>]` lists the sessions.
* `pyle sessions revoke --all | --user <name>` ends sessions, revokes every
  refresh-token family (those tied to a session and those that are not:
  `offline_access`, the device grant) and withdraws authorization, device and
  forward-authentication codes not yet redeemed, for everyone or one account.
  Access tokens already issued live until they expire.  None of these three
  reaches the sessions a relying party (Zulip, say) keeps of its own:
  deactivate the user there too.
* `pyle root-key rotate` replaces the root key: everything sealed under it is
  re-sealed under a new one in one transaction, recovery codes (keyed by it,
  and not re-keyable) are deleted, forward-authentication cookies stop
  verifying, and the old key file's bytes are zeroed as far as the filesystem
  allows.  A running server picks up the new key with its next request.
  Take a fresh backup afterwards, and destroy the other copies of the old key.
* `pyle root-key check` checks the key file against the database, finishing
  a rotation that stopped before installing its key.
* `pyle invite <name> [--group <group>]… [--ttl <7d>] [--email <e>]
  [--display-name <n>]` prints a link that creates the account `<name>` with
  its first way in, and with that address and display name.
* Group names (`--group`, for `user add` and `invite`) are 1 to 64 letters,
  digits, `-`, `_` and `.`, starting with a letter or digit
  (`Config.validGroupName`); members of `adminGroup` (`admin`) may use the
  administration pages under `/admin`.
* `pyle audit verify` checks the audit log's hash chain.
* `pyle client add <id> --redirect <uri>… [--public] [--scope <s>]… [--name <n>]
  [--rs256] [--post-logout <uri>]… [--min-acr <level>]` registers an OpenID
  Connect client and prints its secret, once.  `--min-acr` is the lowest level
  a session must reach to sign in to it: `mfa` (the default), `phr` or `phrh`,
  or the identifier of one.
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
  "  user add <name> [--group <g>]... [--email <e>] [--display-name <n>]\n" ++
  "                                    create an account\n" ++
  "  user set <name> [--email <e> | --no-email] [--display-name <n> | --no-display-name]\n" ++
  "                                    set or clear an account's email and display name\n" ++
  "  user list                         list the accounts\n" ++
  "  user disable <name>               disable an account and end its sessions and tokens\n" ++
  "  user enable <name>                enable a disabled account again\n" ++
  "  user remove <name> --yes          delete an account and everything that is its\n" ++
  "  sessions list [--user <name>]     list the sessions, everyone's or one account's\n" ++
  "  sessions revoke --all | --user <name>\n" ++
  "                                    end sessions, refresh tokens (offline_access too)\n" ++
  "                                    and pending codes\n" ++
  "  invite <name> [--group <g>]... [--ttl <7d>] [--email <e>] [--display-name <n>]\n" ++
  "                                    print a link that creates an account\n" ++
  "  audit verify                      check the audit log's hash chain\n" ++
  "  client add <id> --redirect <uri>... [--public] [--scope <s>]... [--name <n>]\n" ++
  "             [--rs256] [--post-logout <uri>]... [--min-acr mfa|phr|phrh]\n" ++
  "                                    register an OpenID Connect client\n" ++
  "  client list                       list the clients\n" ++
  "  client remove <id>                remove a client and its tokens\n" ++
  "  keys rotate [es256|rs256|biscuit] promote the next signing key, announce a new one\n" ++
  "  keys list                         list the signing keys\n" ++
  "  root-key rotate                   replace the root key, re-sealing everything under it\n" ++
  "  root-key check                    check the root key file against the database\n" ++
  "  version                           print the version\n\n" ++
  "The configuration file defaults to $PYLE_CONFIG, then ./pyle.json.\n\n" ++
  "Warning: services such as Zulip key accounts by email address.  Moving an address\n" ++
  "from one account to another (user set) hands the second account whatever the\n" ++
  "first had in those services."

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
  discard <| RootKey.resolve store config.rootKeyFile (← Http.systemClock)
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
def userAdd (path : System.FilePath) (name : String) (groups : List String)
    (email displayName : Option String) : IO UInt32 := do
  let store ← openStore path
  let now ← Http.systemClock
  let u ← store.addUser name groups now email displayName
  discard <| Audit.append store now
    { event := .userAdded, outcome := .success, userName := some u.name, clientAddress := "cli",
      detail := Audit.contactDetail u.email u.displayName }
  IO.println s!"pyle: created {u.name} (id {u.id})"
  return 0

/-- A change `pyle user set` makes to an optional field: set it, clear it, or
leave it.  The last value given counts, as for the other flags. -/
def fieldChange (what : String) (values : List String) (clear : Bool) :
    Except String (Option (Option String)) :=
  match values, clear with
  | [], false => .ok none
  | [], true => .ok (some none)
  | _ :: _, true => .error s!"give --{what} or --no-{what}, not both"
  | _ :: _, false => .ok (some values.getLast?)

/-- `pyle user set`: set or clear an account's email address and display
name, both in one transaction, each change audited with the old and the new
value. -/
def userSet (path : System.FilePath) (name : String) (emails displayNames : List String)
    (noEmail noDisplayName : Bool) : IO UInt32 := do
  let changes := do
    return (← fieldChange "email" emails noEmail,
      ← fieldChange "display-name" displayNames noDisplayName)
  let (email, displayName) ← match changes with
    | .ok c => pure c
    | .error e =>
      IO.eprintln s!"pyle: {e}"
      return 2
  if email.isNone && displayName.isNone then
    IO.eprintln "pyle: nothing to change: give --email, --no-email, --display-name or \
      --no-display-name"
    return 2
  let store ← openStore path
  let noUser : IO UInt32 := do
    IO.eprintln s!"pyle: there is no user named '{name}'"
    return 1
  let some u ← store.findUserByName name | noUser
  let some (before, after) ← store.setUserContact u.id email displayName | noUser
  let now ← Http.systemClock
  let changes := Audit.contactChanges before after
  for detail in changes do
    discard <| Audit.append store now
      { event := .userChanged, outcome := .success, userName := some u.name,
        clientAddress := "cli", detail }
  if changes.isEmpty then IO.println s!"pyle: {u.name}: nothing changed"
  IO.println s!"pyle: {after.name}: email {after.email.getD "-"}, display name \
    {after.displayName.getD "-"}"
  return 0

/-- `pyle user list`. -/
def userList (path : System.FilePath) : IO UInt32 := do
  let store ← openStore path
  for u in ← store.listUsers do
    let n ← store.authenticatorCount u.id
    let groups := if u.groups.isEmpty then "-" else ",".intercalate u.groups
    let state := if u.disabled then " (disabled)" else ""
    IO.println s!"{u.name}\tgroups: {groups}\tauthenticators: {n}\temail: \
      {u.email.getD "-"}\tdisplay name: {u.displayName.getD "-"}{state}"
  return 0

/-- `pyle client add`. -/
def clientAdd (path : System.FilePath) (id : String)
    (redirects scopes names postLogout : List String) (isPublic rs256 : Bool)
    (minAcr : Option String) : IO UInt32 := do
  let minAcr ← match minAcr with
    | none => pure Acr.mfa
    | some m => match Acr.ofIdentifier? m with
      | some a => pure a
      | none =>
        IO.eprintln s!"pyle: '{m}' is not a level (mfa, phr or phrh)"
        return 2
  let store ← openStore path
  let settings : Store.ClientSettings :=
    { idTokenAlg := if rs256 then "RS256" else "ES256", postLogoutRedirectUris := postLogout,
      minAcr }
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
    IO.println s!"{c.id}\t{kind}\t{settings.idTokenAlg}\tmin-acr: {settings.minAcr.shortName}\t\
      scopes: {" ".intercalate c.scopes}\tredirects: {" ".intercalate c.redirectUris}"
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
  let rootKey ← RootKey.resolve store config.rootKeyFile (← Http.systemClock)
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

/-- `pyle root-key rotate`: replace the root key and re-seal everything under
the new one (`RootKey.rotate`). -/
def rootKeyRotate (path : System.FilePath) : IO UInt32 := do
  let config ← Config.load path
  let store ← Store.Store.openAt config.database (← Http.systemClock)
  let rot ← RootKey.rotate store config.rootKeyFile (← Http.systemClock)
  let r := rot.resealed
  IO.println s!"pyle: replaced the root key {RootKey.showId rot.oldId} by \
    {RootKey.showId rot.newId} in {config.rootKeyFile}"
  IO.println "pyle: the old key file's bytes were zeroed, as far as the filesystem allows: \
    a copy-on-write filesystem, an SSD or a snapshot may keep them.  Destroy every other \
    copy of the old key too, in backups included, unless you mean to keep it with the \
    backups it opens"
  IO.println s!"pyle: re-sealed {r.keys} signing keys (the same kids) and {r.totpApps} \
    authenticator apps"
  IO.println s!"pyle: deleted {r.recoveryCodes} recovery codes of {r.recoveryAccounts} \
    accounts: they were keyed by the old root key; the account page asks for new ones"
  IO.println "pyle: forward-authentication cookies no longer verify: protected hosts send \
    their users round the grant once more"
  IO.println "pyle: a running server picks up the new key with its next request"
  IO.println s!"pyle: take a fresh backup now, of the database and of the new key \
    {config.rootKeyFile}: older backups of the database open only under the old key"
  return 0

/-- `pyle root-key check`: the key file against the database, finishing a
rotation that stopped before installing its key. -/
def rootKeyCheck (path : System.FilePath) : IO UInt32 := do
  let config ← Config.load path
  let store ← Store.Store.openAt config.database (← Http.systemClock)
  let key ← RootKey.resolve store config.rootKeyFile (← Http.systemClock)
  IO.println s!"pyle: {config.rootKeyFile} is the root key of {config.database} \
    (fingerprint {RootKey.showId (Store.rootKeyId key)})"
  return 0

/-- The account named `name`, or a message and `none`. -/
def findNamed (store : Store.Store) (name : String) : IO (Option Store.User) := do
  let u ← store.findUserByName name
  if u.isNone then IO.eprintln s!"pyle: there is no user named '{name}'"
  return u

/-- What ending access came to, as `pyle` says it. -/
def describe (r : Store.Revocation) : String :=
  s!"{r.sessions} sessions, {r.families} refresh-token families and {r.codes} pending codes"

/-- What ending access in pyle does not do. -/
def relyingParties : String :=
  "pyle: this ends pyle's sessions and the tokens pyle issued, not the sessions services \
    such as Zulip keep of their own: deactivate the user there too"

/-- `pyle sessions list [--user <name>]`. -/
def sessionsList (path : System.FilePath) (user : Option String) : IO UInt32 := do
  let store ← openStore path
  let names := (← store.listUsers).toList.map fun u => (u.id, u.name)
  let rows ← match user with
    | some n =>
      let some u ← findNamed store n | return 1
      store.listSessions u.id
    | none => store.listAllSessions
  for s in rows do
    let who := (names.lookup s.user).getD s!"#{s.user}"
    IO.println s!"{who}\tsigned in {s.authTime}\tlast seen {s.lastSeen}\tamr: \
      {",".intercalate s.amr}\tfrom {s.clientAddress}\t{s.userAgent}"
  return 0

/-- `pyle sessions revoke --all | --user <name>`. -/
def sessionsRevoke (path : System.FilePath) (all : Bool) (user : Option String) :
    IO UInt32 := do
  if all == user.isSome then
    IO.eprintln "pyle: give --all or --user <name>, one of them"
    return 2
  let store ← openStore path
  let target ← match user with
    | some n =>
      let some u ← findNamed store n | return 1
      pure (some u)
    | none => pure none
  let r ← Admin.revokeSessions store target (← Http.systemClock)
  let whose := match target with
    | some u => u.name
    | none => "every account"
  IO.println s!"pyle: ended {describe r} of {whose}"
  IO.println "pyle: access tokens already issued live until they expire (accessTokenSeconds)"
  IO.println relyingParties
  return 0

/-- `pyle user disable <name>`. -/
def userDisable (path : System.FilePath) (name : String) : IO UInt32 := do
  let store ← openStore path
  let some u ← findNamed store name | return 1
  let some r ← Admin.disableUser store u (← Http.systemClock) | return 1
  IO.println s!"pyle: disabled {u.name}, and ended {describe r}"
  IO.println relyingParties
  return 0

/-- `pyle user enable <name>`. -/
def userEnable (path : System.FilePath) (name : String) : IO UInt32 := do
  let store ← openStore path
  let some u ← findNamed store name | return 1
  unless ← Admin.enableUser store u (← Http.systemClock) do return 1
  IO.println s!"pyle: enabled {u.name}"
  return 0

/-- `pyle user remove <name> --yes`. -/
def userRemove (path : System.FilePath) (name : String) (yes : Bool) : IO UInt32 := do
  unless yes do
    IO.eprintln s!"pyle: removing {name} deletes the account and everything that is its, for \
      good; run it again with --yes"
    return 2
  let store ← openStore path
  let some u ← findNamed store name | return 1
  let some r ← Admin.removeUser store u (← Http.systemClock) | return 1
  IO.println s!"pyle: removed {u.name} (email {u.email.getD "-"}), and ended {describe r}; \
    deleted {r.invitations} pending invitations for the name or address"
  IO.println relyingParties
  IO.println "pyle: the name and the address are free now; a service that keys accounts by \
    either hands whoever gets them next what this account had there"
  return 0

/-- `pyle invite`: issue an invitation and print its link.  `ttl` is a
lifetime such as `7d` or `12h`; seven days if not given. -/
def invite (path : System.FilePath) (name : String) (groups : List String)
    (ttl email displayName : Option String) : IO UInt32 := do
  let seconds ← match ttl with
    | none => pure (7 * 86400)
    | some t => match SignIn.parseDuration t with
      | some n => pure n
      | none =>
        IO.eprintln s!"pyle: '{t}' is not a lifetime (a number followed by d, h, m or s)"
        return 2
  let config ← Config.load path
  let store ← Store.Store.openAt config.database (← Http.systemClock)
  let now ← Http.systemClock
  let url ← SignIn.createInvitation store config.issuer name groups seconds now
    (email := email) (displayName := displayName)
  let (email, displayName) ← Store.normalizeContact email displayName
  let contact := Audit.contactDetail email displayName
  discard <| Audit.append store now
    { event := .userChanged, outcome := .success, userName := some name,
      clientAddress := "cli", detail := if contact.isEmpty then "invited"
        else s!"invited; {contact}" }
  IO.println url
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
  let (ttls, args) := takeFlag "--ttl" args
  let (minAcrs, args) := takeFlag "--min-acr" args
  let (emails, args) := takeFlag "--email" args
  let (displayNames, args) := takeFlag "--display-name" args
  let (noEmail, args) := takeSwitch "--no-email" args
  let (noDisplayName, args) := takeSwitch "--no-display-name" args
  let (users, args) := takeFlag "--user" args
  let (all, args) := takeSwitch "--all" args
  let (yes, args) := takeSwitch "--yes" args
  -- Likewise --user, --all and --yes, which mean something to one or two
  -- commands each, and could do harm if a typo sent them elsewhere.
  let (takesUser, takesAll, takesYes) := match args with
    | ["sessions", "list"] => (true, false, false)
    | ["sessions", "revoke"] => (true, true, false)
    | ["user", "remove", _] => (false, false, true)
    | _ => (false, false, false)
  if (!takesUser && !users.isEmpty) || (!takesAll && all) || (!takesYes && yes) then
    IO.eprintln "pyle: --user is for sessions list and sessions revoke, --all for sessions \
      revoke, --yes for user remove"
    return 2
  -- The contact flags mean something to three commands, and the clearing ones
  -- to one; anywhere else they would be silently ignored, so they are refused.
  let (takesContact, takesClear) := match args with
    | ["user", "set", _] => (true, true)
    | ["user", "add", _] | ["invite", _] => (true, false)
    | _ => (false, false)
  if (!takesContact && (!emails.isEmpty || !displayNames.isEmpty)) ||
      (!takesClear && (noEmail || noDisplayName)) then
    IO.eprintln "pyle: --email and --display-name are for user add, user set and invite; \
      --no-email and --no-display-name for user set only"
    return 2
  -- Groups reach Remote-Groups, datalog and tokens: only names of the plain
  -- alphabet are given out.
  if let some g := groups.find? (!Config.validGroupName ·) then
    IO.eprintln s!"pyle: '{g}' is not a group name (letters, digits, '-', '_' and '.', at \
      most 64, starting with a letter or digit)"
    return 2
  try
    match args with
    | ["version"] =>
      IO.println "pyle 0.1.0"
      return 0
    | ["init"] => init (← configPath configs)
    | ["serve"] =>
      Server.run (← Config.load (← configPath configs))
      return 0
    | ["user", "add", name] =>
      userAdd (← configPath configs) name groups emails.getLast? displayNames.getLast?
    | ["user", "set", name] =>
      userSet (← configPath configs) name emails displayNames noEmail noDisplayName
    | ["user", "list"] => userList (← configPath configs)
    | ["user", "disable", name] => userDisable (← configPath configs) name
    | ["user", "enable", name] => userEnable (← configPath configs) name
    | ["user", "remove", name] => userRemove (← configPath configs) name yes
    | ["sessions", "list"] => sessionsList (← configPath configs) users.getLast?
    | ["sessions", "revoke"] => sessionsRevoke (← configPath configs) all users.getLast?
    | ["root-key", "rotate"] => rootKeyRotate (← configPath configs)
    | ["root-key", "check"] => rootKeyCheck (← configPath configs)
    | ["invite", name] =>
      invite (← configPath configs) name groups ttls.getLast? emails.getLast?
        displayNames.getLast?
    | ["audit", "verify"] => auditVerify (← configPath configs)
    | ["client", "add", id] =>
      clientAdd (← configPath configs) id redirects scopes names postLogout isPublic rs256
        minAcrs.getLast?
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