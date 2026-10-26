import Pyle.SignIn.Endpoints
import Pyle.Account.Endpoints
import Pyle.Web.Pages

/-!
# The sign-in routes

Everything DESIGN §1–§4 adds to the server, as one list that
`Pyle.Server.routes` appends: the pages, their assets, the sign-in and
step-up ceremonies, invitations and account management.  Every `POST` here
takes part in the `Origin` check; none is exempt, since all of them are
called by pyle's own pages.
-/

namespace Pyle
namespace SignIn

open Http

/-- The routes of sign-in, invitations, the account and the pages. -/
def routes : List Route := [
  .mk' .get "/" Web.root,
  .mk' .get "/assets/pyle.js" Web.scriptAsset,
  .mk' .get "/assets/pyle.css" Web.stylesheetAsset,
  .mk' .get "/signin" Web.signIn,
  .mk' .post "/signin/webauthn/begin" beginSignIn,
  .mk' .post "/signin/webauthn/finish" (finishAssertion .authenticate),
  .mk' .post "/signin/stepup/begin" beginStepUp,
  .mk' .post "/signin/stepup/finish" (finishAssertion .stepUp),
  .mk' .post "/signin/codes" signInWithCodes,
  .mk' .get "/invite/:token" Web.invite,
  .mk' .post "/invite/:token/begin" beginInvitation,
  .mk' .post "/invite/:token/finish" finishInvitation,
  .mk' .post "/invite/:token/password" finishInvitationPassword,
  .mk' .get "/account" Web.account,
  .mk' .post "/account/authenticators/register/begin" Account.registerBegin,
  .mk' .post "/account/authenticators/register/finish" Account.registerFinish,
  .mk' .post "/account/authenticators/rename" Account.rename,
  .mk' .post "/account/authenticators/remove" Account.remove,
  .mk' .post "/account/totp/begin" Account.totpBegin,
  .mk' .post "/account/totp/confirm" Account.totpConfirm,
  .mk' .post "/account/totp/remove" Account.totpRemove,
  .mk' .post "/account/recovery-codes" Account.recoveryCodes,
  .mk' .post "/account/password" Account.setPassword,
  .mk' .post "/account/password/remove" Account.removePassword,
  .mk' .post "/account/sessions/end" Account.endSession
]

end SignIn
end Pyle