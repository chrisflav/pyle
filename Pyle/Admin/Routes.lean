import Pyle.Admin.Pages

/-!
# The administration routes

The pages and endpoints under `/admin`, as one list that `Pyle.Server.routes`
appends, and `hiddenFrom`, which `Pyle.Server.route` asks before routing a
request: for anyone but an administrator, every path under `/admin` — a page,
an endpoint, the script, a path that names nothing, a method no route takes,
a `POST` from another origin — is the `404` of a path that does not exist.
The handlers check again for themselves (`withAdministrator`,
`withAdministratorPage`), and every `POST` here takes part in the `Origin`
check.
-/

namespace Pyle
namespace Admin

open Http

/-- Whether a path is under `/admin`, as the router reads paths: its first
segment is `admin`. -/
def isAdminPath (path : String) : Bool :=
  match pathSegments path with
  | some ("admin" :: _) => true
  | _ => false

/-- Whether a request is for a path under `/admin` from someone who is not an
administrator (`administrator`), who is to be told nothing is there. -/
def hiddenFrom (ctx : Ctx) (r : Req) : IO Bool := do
  if !isAdminPath r.path then return false
  return (← administrator ctx r).isNone

/-- The administration routes. -/
def routes : List Route := [
  .mk' .get "/admin" usersPage,
  .mk' .get "/admin/users/:name" userPage,
  .mk' .get "/admin/invitations" invitationsPage,
  .mk' .get "/admin/clients" clientsPage,
  .mk' .get "/admin/clients/:id" clientPage,
  .mk' .get "/admin/audit" auditPage,
  .mk' .get "/admin/keys" keysPage,
  .mk' .get "/admin/assets/admin.js" scriptAsset,
  .mk' .post "/admin/users/contact" setContact,
  .mk' .post "/admin/users/groups" setGroups,
  .mk' .post "/admin/users/disable" disable,
  .mk' .post "/admin/users/enable" enable,
  .mk' .post "/admin/users/revoke" revoke,
  .mk' .post "/admin/users/sessions/end" endSession,
  .mk' .post "/admin/users/remove" remove,
  .mk' .post "/admin/invitations/create" createInvitation,
  .mk' .post "/admin/invitations/revoke" revokeInvitation,
  .mk' .post "/admin/clients/add" addClient,
  .mk' .post "/admin/clients/update" updateClient,
  .mk' .post "/admin/clients/remove" removeClient,
  .mk' .post "/admin/keys/rotate" rotateKeys
]

end Admin
end Pyle
