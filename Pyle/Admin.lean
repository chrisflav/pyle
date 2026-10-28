import Pyle.Audit

/-!
# Administration: ending access, disabling and removing accounts

What `pyle sessions revoke`, `pyle user disable`, `pyle user enable` and
`pyle user remove` do, each in one transaction together with its audit entry,
so that the log says what was done exactly when it was done.

Ending access (`Store.endAccessIn`) ends sessions, revokes every
refresh-token family — those tied to a session and those that are not, from
`offline_access` or the device grant — and withdraws codes not yet redeemed.
Access tokens already issued are biscuits that services check offline: they
live until they expire (`accessTokenSeconds`), though `/userinfo` and the
kleis attestation refuse a disabled or removed account's at once.

**Only pyle's own.**  None of this reaches into a relying party: a session
a user already has at Zulip, say, is that service's, and lives on until the
service ends it.  Deactivate the user there too.  And `user remove` frees the
account's name and email address for another account, which services that
key accounts by either would take for the removed one (README, the warning
under Usage).
-/

namespace Pyle
namespace Admin

open Store

/-- The audit log's account of a revocation. -/
def revocationDetail (r : Revocation) : String :=
  s!"{r.sessions} sessions, {r.families} refresh-token families and {r.codes} pending codes \
    ended"

/-- End the sessions, refresh-token families and pending codes of one
account, or of every account when `user` is `none`. -/
def revokeSessions (store : Store) (user : Option User) (now : Nat) : IO Revocation :=
  store.atomically fun c => do
    let r ← endAccessIn c (user.map (·.id)) now
    discard <| Audit.appendIn c now
      { event := .sessionsRevoked, outcome := .success, userName := user.map (·.name),
        clientAddress := "cli",
        detail := revocationDetail r ++ (if user.isNone then " for every account" else "") }
    return r

/-- Disable an account, ending its access; `none` if it does not exist. -/
def disableUser (store : Store) (u : User) (now : Nat) : IO (Option Revocation) :=
  store.atomically fun c => do
    let some r ← setUserDisabledIn c u.id true now | return none
    discard <| Audit.appendIn c now
      { event := .userChanged, outcome := .success, userName := some u.name,
        clientAddress := "cli", detail := s!"disabled; {revocationDetail r}" }
    return some r

/-- Enable an account again.  Whether it exists. -/
def enableUser (store : Store) (u : User) (now : Nat) : IO Bool :=
  store.atomically fun c => do
    let some _ ← setUserDisabledIn c u.id false now | return false
    discard <| Audit.appendIn c now
      { event := .userChanged, outcome := .success, userName := some u.name,
        clientAddress := "cli", detail := "enabled" }
    return true

/-- Remove an account and everything that is its, recording its name and
email address in the audit log; `none` if it does not exist. -/
def removeUser (store : Store) (u : User) (now : Nat) : IO (Option Revocation) :=
  store.atomically fun c => do
    let some (gone, r) ← removeUserIn c u.id now | return none
    discard <| Audit.appendIn c now
      { event := .userRemoved, outcome := .success, userName := some gone.name,
        clientAddress := "cli",
        detail := s!"email: {Audit.showEmail gone.email}; {revocationDetail r}; \
          {r.invitations} pending invitations for the name or address deleted" }
    return some r

/-! ## Administrators

Who may use the administration pages: an enabled account in the configured
`adminGroup`.  The pages refuse to leave a deployment without one — the last
enabled administrator cannot be disabled, removed or taken out of the group,
by someone else or by themselves — so that the pages never lock everyone out
of themselves.  The command line is not held to this: it is how a deployment
that has lost its administrators gets one back. -/

/-- Whether an account is an administrator: enabled, and in `group`. -/
def isAdministrator (group : String) (u : User) : Bool :=
  !u.disabled && u.groups.contains group

/-- The enabled accounts in `group`, on a connection (inside the transaction
that is about to change one of them). -/
def administratorsIn (c : SQLite) (group : String) : IO (List User) := do
  let users ← query c s!"SELECT {userColumns} FROM users WHERE disabled = 0" #[] readUser
  return users.toList.filter (isAdministrator group)

/-- Whether an administrator other than `u` would be left: true when `u` is
not one now, and otherwise when another enabled account is in `group`. -/
def leavesAnotherAdministrator (c : SQLite) (group : String) (u : UserId) : IO Bool := do
  let admins ← administratorsIn c group
  return !admins.any (·.id == u) || admins.any (·.id != u)

end Admin
end Pyle
