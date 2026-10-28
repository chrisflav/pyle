import Pyle.Admin
import Pyle.SignIn.Invite
import Pyle.Oidc.Client
import Pyle.Keys.Lifecycle

/-!
# The administration endpoints

What an administrator does from the pages under `/admin` (`Pyle.Admin.Pages`),
as JSON over `fetch`: the same changes the command line makes, each audited
with the administrator as the entry's user and what was changed at the start
of its detail (`account bob: disabled; …`, `client wiki: removed`).

**Who may.**  `rule` is all of it, stated on its own so that it can be
read and proved about:

* a request whose session is not an administrator's — no session, an
  account not in `adminGroup`, a disabled one — is answered `404`, by every
  path under `/admin`, so that the pages do not tell anyone else they exist
  (`Admin.Routes.hiddenFrom` does this before routing, so that no `405` or
  `Origin` refusal says otherwise);
* an administrator's session below `phr` — not signed in with a passkey — is
  sent to sign in again at `phr` (a page), or answered `403
  step_up_required` (an endpoint), and the page's script then confirms with a
  passkey and tries again;
* every endpoint here changes something, and so also needs a sign-in within
  the last five minutes (`SignIn.stepUpSeconds`), as the account endpoints
  do: `403 step_up_required` otherwise.

Every endpoint is a `POST` and takes part in the `Origin` check, and is counted
against the rate limiter for the administrator's account and address
(`SignIn.limited`): a refused request counts as a failure, a successful one
does not.

**The last administrator.**  An administrator cannot be disabled, removed or
taken out of `adminGroup` when no other enabled administrator would be left
(`leavesAnotherAdministrator`): `409 last_administrator`.  This holds for an
administrator acting on their own account too.  The check and the change are
one transaction.

**Secrets.**  A confidential client's secret and an invitation's link are in
the answer that makes them and nowhere else: not in the audit log, not in any
page.  Pending invitations are named by the hash of their token, which opens
nothing.

| | body | answer |
| --- | --- | --- |
| `/admin/users/contact` | `{"name", "email"?, "displayName"?}` (`null` or `""` clears) | `200` the account, or `409 email_taken` |
| `/admin/users/groups` | `{"name", "groups"}` | `200` the account, or `409 last_administrator` |
| `/admin/users/disable`, `…/enable` | `{"name"}` | `200` what ended; `204` |
| `/admin/users/revoke` | `{"name"}` | `200` what ended |
| `/admin/users/sessions/end` | `{"name", "handle"}` | `204` |
| `/admin/users/remove` | `{"name", "confirm"}` (`confirm` = `name`) | `200` what ended |
| `/admin/invitations/create` | `{"name", "email"?, "displayName"?, "groups"?, "ttl"?}` | `201 {"url", "name", "expires"}` |
| `/admin/invitations/revoke` | `{"handle"}` | `204` |
| `/admin/clients/add` | `{"id", "name"?, "redirectUris", "postLogoutUris"?, "scopes"?, "public"?, "rs256"?, "minAcr"?}` | `201 {"id", "secret"?}` |
| `/admin/clients/update` | `{"id", "name"?, "redirectUris"?, "postLogoutUris"?, "scopes"?, "minAcr"?}` | `204` |
| `/admin/clients/remove` | `{"id", "confirm"}` (`confirm` = `id`) | `204` |
| `/admin/keys/rotate` | `{"use"?}` (`es256`, `rs256`, `biscuit`; all three without) | `{"rotated"}` |
-/

namespace Pyle
namespace Admin

open Http Store SignIn
open Lean (Json toJson)

/-! ## Who may -/

/-- What the administration pages do with a request. -/
inductive Decision where
  /-- Not an administrator's: `404`, as if there were nothing here. -/
  | hidden
  /-- An administrator's session below `phr`: sign in again at `phr`. -/
  | belowPhr
  /-- A change, from a session that has not signed in within the step-up
  window: `403 step_up_required`. -/
  | notFresh
  /-- Go ahead. -/
  | allow
  deriving DecidableEq, Repr

/-- The rule: an administrator (`admin`, from `isAdministrator`), at `phr` or
better, and for a change (`mutating`) signed in within the step-up window
(`fresh`). -/
def rule (admin : Bool) (level : Acr) (fresh mutating : Bool) : Decision :=
  if !admin then .hidden
  else if !level.satisfies .phr then .belowPhr
  else if mutating && !fresh then .notFresh
  else .allow

/-- Anyone who is not an administrator is shown nothing. -/
theorem rule_hidden (level : Acr) (fresh mutating : Bool) :
    rule false level fresh mutating = .hidden := rfl

/-- What going ahead takes: an administrator, a session at `phr` or better,
and for a change a fresh sign-in. -/
theorem rule_allow {admin fresh mutating : Bool} {level : Acr}
    (h : rule admin level fresh mutating = .allow) :
    admin = true ∧ Acr.phr ≤ level ∧ (mutating = true → fresh = true) := by
  unfold rule at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2 h3
        refine ⟨by simpa using h1, Acr.satisfies_iff.mp (by simpa using h2), ?_⟩
        intro hm
        simpa [hm] using h3

/-- The request's session and its account, if the account is an
administrator's (`isAdministrator`).  A disabled account has no session to
begin with (`Store.touchSession`), and is no administrator either. -/
def administrator (ctx : Ctx) (r : Req) : IO (Option (Session × User)) := do
  let some s ← Session.current ctx r | return none
  let some u ← ctx.store.findUser s.user | return none
  return if isAdministrator ctx.config.adminGroup u then some (s, u) else none

/-- The decision for a request, and the administrator's session and account
when there is one. -/
def decision (ctx : Ctx) (r : Req) (mutating : Bool) :
    IO (Decision × Option (Session × User)) := do
  match ← administrator ctx r with
  | none => return (.hidden, none)
  | some (s, u) =>
    let fresh := Session.authenticatedWithin s (← ctx.clock) stepUpSeconds
    return (rule true s.level fresh mutating, some (s, u))

/-- The `404` of a path that does not exist, word for word the router's. -/
def hidden : Reply := Reply.error .notFound "not_found"

/-- Run `act` for an administrator's change: `404` for anyone else, `403
step_up_required` below `phr` or without a fresh sign-in, then the body as
JSON, counted against the rate limiter for the administrator (`event` is what
a refusal by the limiter is audited as).  A reply below `400` takes the
attempt back. -/
def withAdministrator (ctx : Ctx) (r : Req) (event : Audit.Event)
    (act : Session → User → Json → IO Reply) : IO Reply := do
  match ← decision ctx r (mutating := true) with
  | (.allow, some (s, u)) =>
    let j ← match jsonBody r with
      | .ok j => pure j
      | .error rep => return rep
    limited ctx r event (some u.name) fun lim attempt => do
      let rep ← act s u j
      if rep.status.toCode < 400 then lim.succeed attempt
      return rep
  | (.hidden, _) | (_, none) => return hidden
  | _ => return stepUpRequired

/-! ## Replies and the audit log -/

/-- `409`, for a change that would leave no enabled administrator. -/
def lastAdministrator : Reply :=
  Reply.error .conflict "last_administrator"
    "this is the last enabled administrator; make another one first"

/-- `404`, for an account that does not exist. -/
def noSuchAccount : Reply := Reply.error .notFound "not_found" "no such account"

/-- `404`, for a client that does not exist. -/
def noSuchClient : Reply := Reply.error .notFound "not_found" "no such client"

/-- Record what an administrator did: the administrator as the entry's user,
the request's address, and `detail`, which starts with what it was done
to. -/
def audit (ctx : Ctx) (r : Req) (admin : User) (event : Audit.Event) (outcome : Audit.Outcome)
    (detail : String) : IO Unit :=
  Audit.log ctx r event outcome (userName := some admin.name) (detail := detail)

/-- `audit`, inside the transaction that makes the change. -/
def auditIn (c : SQLite) (now : Nat) (r : Req) (admin : User) (event : Audit.Event)
    (outcome : Audit.Outcome) (detail : String) : IO Unit :=
  discard <| Audit.appendIn c now
    { event, outcome, userName := some admin.name, clientAddress := r.clientAddress, detail }

/-- A list as the audit log and the pages write it: joined with `sep`, or
`none`. -/
def showList (xs : List String) (sep : String := ", ") : String :=
  if xs.isEmpty then "none" else sep.intercalate xs

/-- What ending access came to, as an answer. -/
def revocationJson (r : Revocation) : Json :=
  Json.mkObj [("sessions", toJson r.sessions), ("families", toJson r.families),
    ("codes", toJson r.codes)]

/-- An account as an answer: what the pages show of it. -/
def userJson (u : User) : Json :=
  Json.mkObj [("name", u.name), ("email", toJson u.email), ("displayName", toJson u.displayName),
    ("groups", toJson u.groups), ("disabled", toJson u.disabled)]

/-- Clear the session cookie when the account acted on is the
administrator's own: its sessions have just ended. -/
def forSelf (s : Session) (u : User) (rep : Reply) : Reply :=
  if s.user == u.id then rep.clearSession else rep

/-! ## Reading a body -/

/-- The account a body names by `"name"`. -/
def targetOf (ctx : Ctx) (j : Json) : IO (Except Reply User) := do
  let some name := strField j "name" | return .error (badRequest "'name' is missing")
  match ← ctx.store.findUserByName name.trimAscii.toString with
  | some u => return .ok u
  | none => return .error noSuchAccount

/-- A change to an optional text field: absent leaves it (`none`), `null` or
text that is empty once trimmed clears it, other text sets it. -/
def fieldChange (j : Json) (k : String) : Except Reply (Option (Option String)) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok .null => .ok (some none)
  | .ok (.str s) => .ok (some (if s.trimAscii.isEmpty then none else some s))
  | .ok _ => .error (badRequest s!"'{k}' is not text")

/-- An optional text field: absent, `null` and empty are `none`. -/
def optionalText (j : Json) (k : String) : Except Reply (Option String) :=
  return (← fieldChange j k).bind id

/-- A list of strings, trimmed, without empty ones or repeats: absent is
`none`. -/
def stringsOf (j : Json) (k : String) : Except Reply (Option (List String)) :=
  match j.getObjVal? k with
  | .error _ | .ok .null => .ok none
  | .ok v => match v.getArr? with
    | .ok xs => do
      let ss ← xs.toList.mapM fun
        | .str s => .ok s.trimAscii.toString
        | _ => .error (badRequest s!"'{k}' is not a list of strings")
      return some (ss.filter (!·.isEmpty)).eraseDups
    | .error _ => .error (badRequest s!"'{k}' is not a list of strings")

/-- Groups from a body, each a group name (`Config.validGroupName`). -/
def groupsOf (j : Json) : Except Reply (Option (List String)) := do
  let some gs ← stringsOf j "groups" | return none
  for g in gs do
    unless Config.validGroupName g do
      throw (badRequest s!"'{g}' is not a group name (letters, digits, '-', '_' and '.', at \
        most 64, starting with a letter or digit)")
  return some gs

/-- A boolean member; absent is `false`. -/
def flag (j : Json) (k : String) : Except Reply Bool :=
  match j.getObjVal? k with
  | .error _ | .ok .null => .ok false
  | .ok (.bool b) => .ok b
  | .ok _ => .error (badRequest s!"'{k}' is not true or false")

/-- A level from a body: a short name or an identifier (`Acr.ofIdentifier?`);
absent or empty is `none`. -/
def levelOf (j : Json) (k : String) : Except Reply (Option Acr) := do
  let some t ← optionalText j k | return none
  match Acr.ofIdentifier? t.trimAscii.toString with
  | some a => return some a
  | none => throw (badRequest s!"'{t}' is not a level (mfa, phr or phrh)")

/-- Run a check on a body, answering its `400` if it fails. -/
@[inline] def orReply (x : Except Reply α) (k : α → IO Reply) : IO Reply :=
  match x with
  | .ok a => k a
  | .error rep => return rep

/-! ## Accounts -/

/-- `POST /admin/users/contact`: set or clear an account's email address and
display name (`Store.setUserContact`, which checks both and writes them in
one transaction), auditing each change with the old and the new value. -/
def setContact : Handler := fun ctx r => withAdministrator ctx r .userChanged fun _ admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  orReply (fieldChange j "email") fun email => orReply (fieldChange j "displayName") fun name => do
  if email.isNone && name.isNone then return badRequest "nothing to change"
  -- Checked here too, so that a bad value is a 400 rather than the 409 of an
  -- address another account has.
  if let some (some e) := email then
    if let .error why := normalizeEmail e then return badRequest why
  if let some (some n) := name then
    if let .error why := normalizeDisplayName n then return badRequest why
  let res : Except String (Option (User × User)) ←
    tryCatch (Except.ok <$> ctx.store.setUserContact u.id email name)
      (fun e => pure (.error (toString e)))
  match res with
  | .error why =>
    audit ctx r admin .userChanged .refused s!"account {u.name}: email address taken"
    return Reply.error .conflict "email_taken" why
  | .ok none => return noSuchAccount
  | .ok (some (before, after)) =>
    for d in Audit.contactChanges before after do
      audit ctx r admin .userChanged .success s!"account {u.name}: {d}"
    return .json (userJson after)

/-- What an account change came to. -/
inductive Outcome (α : Type) where
  /-- It was made. -/
  | done (a : α)
  /-- There is no such account. -/
  | missing
  /-- It would leave no enabled administrator, and was not made. -/
  | lastAdministrator

/-- The account with this id, on a connection. -/
def accountIn (c : SQLite) (id : UserId) : IO (Option User) :=
  queryOne c s!"SELECT {userColumns} FROM users WHERE id = ?" #[id] readUser

/-- `POST /admin/users/groups`: replace an account's groups.  Taking the last
enabled administrator out of `adminGroup` is refused. -/
def setGroups : Handler := fun ctx r => withAdministrator ctx r .userChanged fun _ admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  orReply (groupsOf j) fun groups => do
  let some groups := groups | return badRequest "'groups' is missing"
  let group := ctx.config.adminGroup
  let now ← ctx.clock
  let out ← ctx.store.atomically fun c => do
    let some cur ← accountIn c u.id | return Outcome.missing
    if cur.groups.contains group && !groups.contains group &&
        !(← leavesAnotherAdministrator c group u.id) then
      auditIn c now r admin .userChanged .refused
        s!"account {u.name}: leaving {group} would leave no administrator"
      return .lastAdministrator
    discard <| exec c "UPDATE users SET groups = ? WHERE id = ?" #[encodeList groups, u.id]
    if cur.groups != groups then
      auditIn c now r admin .userChanged .success
        s!"account {u.name}: groups: {showList cur.groups} -> {showList groups}"
    return .done { cur with groups }
  match out with
  | .done after => return .json (userJson after)
  | .missing => return noSuchAccount
  | .lastAdministrator => return lastAdministrator

/-- `POST /admin/users/disable`: disable an account and end its access, as
`pyle user disable` does; not the last enabled administrator. -/
def disable : Handler := fun ctx r => withAdministrator ctx r .userChanged fun s admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  let group := ctx.config.adminGroup
  let now ← ctx.clock
  let out ← ctx.store.atomically fun c => do
    unless ← leavesAnotherAdministrator c group u.id do
      auditIn c now r admin .userChanged .refused
        s!"account {u.name}: disabling it would leave no administrator"
      return Outcome.lastAdministrator
    let some rev ← setUserDisabledIn c u.id true now | return .missing
    auditIn c now r admin .userChanged .success
      s!"account {u.name}: disabled; {revocationDetail rev}"
    return .done rev
  match out with
  | .done rev => return forSelf s u (.json (revocationJson rev))
  | .missing => return noSuchAccount
  | .lastAdministrator => return lastAdministrator

/-- `POST /admin/users/enable`: let a disabled account in again. -/
def enable : Handler := fun ctx r => withAdministrator ctx r .userChanged fun _ admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  let now ← ctx.clock
  let found ← ctx.store.atomically fun c => do
    let some _ ← setUserDisabledIn c u.id false now | return false
    auditIn c now r admin .userChanged .success s!"account {u.name}: enabled"
    return true
  return if found then .noContent else noSuchAccount

/-- `POST /admin/users/revoke`: end an account's sessions, refresh-token
families and pending codes, as `pyle sessions revoke --user` does. -/
def revoke : Handler := fun ctx r => withAdministrator ctx r .sessionsRevoked fun s admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  let now ← ctx.clock
  let rev ← ctx.store.atomically fun c => do
    let rev ← endAccessIn c (some u.id) now
    auditIn c now r admin .sessionsRevoked .success s!"account {u.name}: {revocationDetail rev}"
    return rev
  return forSelf s u (.json (revocationJson rev))

/-- `POST /admin/users/sessions/end`: end one of an account's sessions by its
handle (`Session.handle`). -/
def endSession : Handler := fun ctx r => withAdministrator ctx r .signOut fun s admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  let some handle := strField j "handle" | return badRequest "'handle' is missing"
  unless ← Session.terminate ctx u.id handle do
    return Reply.error .notFound "not_found" "no such session"
  audit ctx r admin .signOut .success s!"account {u.name}: a session ended by an administrator"
  return if s.user == u.id && handle == s.handle then Reply.noContent.clearSession
    else .noContent

/-- `POST /admin/users/remove`: delete an account and everything that is its,
as `pyle user remove` does.  `confirm` must be the account's name, as typed;
not the last enabled administrator. -/
def remove : Handler := fun ctx r => withAdministrator ctx r .userRemoved fun s admin j => do
  let u ← match ← targetOf ctx j with
    | .ok u => pure u
    | .error rep => return rep
  if strField j "confirm" != some u.name then
    return Reply.error .badRequest "confirmation_required"
      "type the account's name to confirm that it is to be removed"
  let group := ctx.config.adminGroup
  let now ← ctx.clock
  let out ← ctx.store.atomically fun c => do
    unless ← leavesAnotherAdministrator c group u.id do
      auditIn c now r admin .userRemoved .refused
        s!"account {u.name}: removing it would leave no administrator"
      return Outcome.lastAdministrator
    let some (gone, rev) ← removeUserIn c u.id now | return .missing
    auditIn c now r admin .userRemoved .success
      s!"account {gone.name}: removed; email: {Audit.showEmail gone.email}; \
        {revocationDetail rev}"
    return .done rev
  match out with
  | .done rev => return forSelf s u (.json (revocationJson rev))
  | .missing => return noSuchAccount
  | .lastAdministrator => return lastAdministrator

/-! ## Invitations -/

/-- How long an invitation lives when no `ttl` is given: seven days, as for
`pyle invite`. -/
def defaultInvitationSeconds : Nat := 7 * 86400

/-- `POST /admin/invitations/create`: issue an invitation, as `pyle invite`
does, recorded as the administrator's.  The answer carries the link, which is
not stored and not shown again. -/
def createInvitation : Handler := fun ctx r =>
    withAdministrator ctx r .invitationIssued fun _ admin j => do
  let some name := (strField j "name").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    | return badRequest "'name' is missing"
  unless validUserName name do
    return badRequest s!"'{name}' is not a valid user name (lower-case letters, digits, '-', \
      '_' and '.', at most 64)"
  orReply (groupsOf j) fun groups => orReply (optionalText j "email") fun email =>
    orReply (optionalText j "displayName") fun displayName => orReply (optionalText j "ttl")
    fun ttl => do
  let seconds ← match ttl with
    | none => pure defaultInvitationSeconds
    | some t => match parseDuration t.trimAscii.toString with
      | some n => pure n
      | none => return badRequest s!"'{t}' is not a lifetime (a number followed by d, h, m or s)"
  if (← ctx.store.findUserByName name).isSome then
    return Reply.error .conflict "name_taken" s!"there is already an account named '{name}'"
  let groups := groups.getD []
  let now ← ctx.clock
  let res : Except String String ←
    tryCatch (Except.ok <$> SignIn.createInvitation ctx.store ctx.config.issuer name groups seconds
        now (createdBy := admin.name) (email := email) (displayName := displayName))
      (fun e => pure (.error (toString e)))
  match res with
  | .error why => return badRequest why
  | .ok url =>
    let (email, displayName) ← normalizeContact email displayName
    let contact := Audit.contactDetail email displayName
    audit ctx r admin .invitationIssued .success <|
      s!"invitation for {name}: groups: {showList groups}" ++
      (if contact.isEmpty then "" else s!"; {contact}") ++ s!"; expires {now + seconds}"
    return .json (Json.mkObj [("url", url), ("name", name), ("expires", toJson (now + seconds))])
      .created

/-- The name the pages give a pending invitation: the base64url of its
token's hash (`Store.listInvitations`). -/
def invitationHandle (h : SecretHash) : String := b64 h.bytes

/-- `POST /admin/invitations/revoke`: withdraw a pending invitation by its
handle (`invitationHandle`). -/
def revokeInvitation : Handler := fun ctx r =>
    withAdministrator ctx r .invitationRevoked fun _ admin j => do
  let some handle := strField j "handle" | return badRequest "'handle' is missing"
  let some digest := Encoding.Base64Url.decode handle |>.filter (·.size == 32)
    | return badRequest "'handle' is not an invitation"
  let some inv ← ctx.store.revokeInvitation (.ofStored digest)
    | return Reply.error .notFound "not_found" "no such invitation"
  audit ctx r admin .invitationRevoked .success s!"invitation for {inv.userName}: withdrawn"
  return .noContent

/-! ## Clients -/

/-- A client's settings in the audit log's words. -/
def clientSummary (kind alg : String) (minAcr : Acr) (scopes redirects postLogout : List String) :
    String :=
  s!"{kind}, {alg}, min-acr {minAcr.shortName}; scopes: {showList scopes " "}; \
    redirect URIs: {showList redirects " "}; post-logout URIs: {showList postLogout " "}"

/-- `POST /admin/clients/add`: register a client, as `pyle client add` does
— except that an id already registered is refused (`409`) rather than
replaced, since replacing a client gives it a new secret.  A confidential
client's secret is in the answer once. -/
def addClient : Handler := fun ctx r => withAdministrator ctx r .clientAdded fun _ admin j => do
  let some id := (strField j "id").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    | return badRequest "'id' is missing"
  orReply (optionalText j "name") fun name => orReply (stringsOf j "redirectUris") fun redirects =>
    orReply (stringsOf j "postLogoutUris") fun postLogout => orReply (stringsOf j "scopes")
    fun scopes => orReply (flag j "public") fun isPublic => orReply (flag j "rs256") fun rs256 =>
    orReply (levelOf j "minAcr") fun minAcr => do
  if (← ctx.store.findClient id).isSome then
    return Reply.error .conflict "client_exists"
      s!"there is already a client '{id}'; remove it first to register it again"
  let settings : ClientSettings :=
    { idTokenAlg := if rs256 then "RS256" else "ES256",
      postLogoutRedirectUris := postLogout.getD [], minAcr := minAcr.getD .mfa }
  let name := (name.map (·.trimAscii.toString)).getD id
  let res : Except String (Option String) ←
    tryCatch (Except.ok <$> Oidc.registerClient ctx.store id name (redirects.getD [])
        (scopes.getD []) isPublic settings (← ctx.clock))
      (fun e => pure (.error (toString e)))
  match res with
  | .error why => return badRequest why
  | .ok secret =>
    let some c ← ctx.store.findClient id | return noSuchClient
    audit ctx r admin .clientAdded .success <|
      s!"client {id}: registered, " ++ clientSummary
        (if isPublic then "public" else "confidential") settings.idTokenAlg settings.minAcr
        c.scopes c.redirectUris settings.postLogoutRedirectUris
    return .json (Json.mkObj ([("id", Json.str id)] ++
      (secret.map fun s => ("secret", Json.str s)).toList)) .created

/-- `POST /admin/clients/update`: change a client's name, redirect URIs,
post-logout addresses, scopes and minimum level (`Oidc.updateClient`); what
the body leaves out stays. -/
def updateClient : Handler := fun ctx r =>
    withAdministrator ctx r .clientChanged fun _ admin j => do
  let some id := strField j "id" | return badRequest "'id' is missing"
  let some c ← ctx.store.findClient id | return noSuchClient
  let settings := (← ctx.store.clientSettings id).getD {}
  orReply (optionalText j "name") fun name => orReply (stringsOf j "redirectUris") fun redirects =>
    orReply (stringsOf j "postLogoutUris") fun postLogout => orReply (stringsOf j "scopes")
    fun scopes => orReply (levelOf j "minAcr") fun minAcr => do
  let name := (name.map (·.trimAscii.toString)).getD c.name
  let redirects := redirects.getD c.redirectUris
  let postLogout := postLogout.getD settings.postLogoutRedirectUris
  let scopes := scopes.getD c.scopes
  let minAcr := minAcr.getD settings.minAcr
  let res : Except String Bool ←
    tryCatch (Except.ok <$> Oidc.updateClient ctx.store id name redirects scopes postLogout minAcr)
      (fun e => pure (.error (toString e)))
  match res with
  | .error why => return badRequest why
  | .ok false => return noSuchClient
  | .ok true =>
    let some after ← ctx.store.findClient id | return noSuchClient
    let changes :=
      (if c.name != after.name then [s!"name: \"{c.name}\" -> \"{after.name}\""] else []) ++
      (if c.redirectUris != after.redirectUris then
        [s!"redirect URIs: {showList c.redirectUris " "} -> {showList after.redirectUris " "}"]
        else []) ++
      (if settings.postLogoutRedirectUris != postLogout then
        [s!"post-logout URIs: {showList settings.postLogoutRedirectUris " "} -> \
          {showList postLogout " "}"] else []) ++
      (if c.scopes != after.scopes then
        [s!"scopes: {showList c.scopes " "} -> {showList after.scopes " "}"] else []) ++
      (if settings.minAcr != minAcr then
        [s!"min-acr: {settings.minAcr.shortName} -> {minAcr.shortName}"] else [])
    unless changes.isEmpty do
      audit ctx r admin .clientChanged .success s!"client {id}: {"; ".intercalate changes}"
    return .noContent

/-- `POST /admin/clients/remove`: remove a client and its codes and tokens,
as `pyle client remove` does.  `confirm` must be the client's id, as
typed. -/
def removeClient : Handler := fun ctx r =>
    withAdministrator ctx r .clientRemoved fun _ admin j => do
  let some id := strField j "id" | return badRequest "'id' is missing"
  if strField j "confirm" != some id then
    return Reply.error .badRequest "confirmation_required"
      "type the client's id to confirm that it is to be removed"
  unless ← ctx.store.removeClient id do return noSuchClient
  audit ctx r admin .clientRemoved .success s!"client {id}: removed, with its codes and tokens"
  return .noContent

/-! ## Signing keys -/

/-- `POST /admin/keys/rotate`: rotate the signing keys of one use, or of all
three, as `pyle keys rotate` does: promote the waiting next key, announce a
fresh one. -/
def rotateKeys : Handler := fun ctx r => withAdministrator ctx r .keysRotated fun _ admin j => do
  orReply (optionalText j "use") fun use => do
  let uses ← match use with
    | none => pure Keys.Use.all
    | some n => match Keys.Use.ofName? n.trimAscii.toString with
      | some u => pure [u]
      | none => return badRequest s!"'{n}' is not a key use (es256, rs256, biscuit)"
  let mut out : Array Json := #[]
  for u in uses do
    let rot ← Keys.rotate ctx.store ctx.rootKey u (← ctx.clock)
    let promoted := match rot.promoted with
      | some kid => s!"{kid} is now current"
      | none => "no next key was waiting"
    audit ctx r admin .keysRotated .success
      s!"keys {u.name}: {promoted}; announced {rot.announced} as next"
    out := out.push (Json.mkObj [("use", u.name), ("promoted", toJson rot.promoted),
      ("announced", rot.announced)])
  return .json (Json.mkObj [("rotated", Json.arr out)])

end Admin
end Pyle
