import PyleTests.ForwardAuth

/-!
# Assurance levels

What each level is worth to the services behind pyle (DESIGN.md §1, §5): a
client or a protected host can ask for more than the `mfa` floor, never less;
`acr_values` and the `claims` parameter are read in order, with their
aliases, ignoring what pyle does not know — REFEDS SFA among it;
`prompt=none` answers `interaction_required` for a level too low; the ID
token, the access token, `/userinfo`, the kleis attestation and the
forward-auth policy all state the session's level and the account's strongest
one; the device grant needs `phr` or the client's minimum; and the token
endpoint answers to the client's minimum as it is now.

Sessions below a requirement are made as everywhere, through checked factors:
`weakFor` signs in with a security key without user verification and a TOTP
code, at `mfa`.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open Lean (Json)

/-- The claims of a verified ID token from a token response, or `null`. -/
def idClaims (ctx : Ctx) (t : Reply) : IO Json :=
  return (← verifyEs256 ctx ((jsonStr t "id_token").getD "")).toOption.getD .null

/-- A string claim. -/
def claimStr (claims : Json) (k : String) : Option String := (claims.getObjValAs? String k).toOption

/-- Levels through OpenID Connect. -/
def oidcAssuranceTests : IO Unit := withCtx fun ctx _ => do
  group "assurance: OpenID Connect"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let d := bodyJson (← get ctx "/.well-known/openid-configuration")
  check "discovery lists the four levels" (d.getObjVal? "acr_values_supported" ==
    .ok (Json.arr #["https://refeds.org/profile/mfa", "phr", "phrh"]))
  check "and supports the claims parameter"
    (d.getObjVal? "claims_parameter_supported" == .ok (Json.bool true))
  check "and names the account claim"
    (((d.getObjValAs? (List String) "claims_supported").toOption.getD []).contains
      "pyle_account_acr")
  -- Per-client minimums.
  let some vaultSecret ← registerClient ctx.store "vault" "Vault" [appRedirect] [] false
      { minAcr := .phr } 1
    | check "vault registers" false
  checkEq "the minimum is stored" ((← ctx.store.clientSettings "vault").map (·.minAcr))
    (some .phr)
  let weak ← weakFor ctx alice
  let r ← get ctx (authorizeUrl "vault") weak
  checkEq "a client with phr as its minimum sends an mfa session to sign in"
    (param (location r) "acr") (some "phr")
  check "the default client takes it" (param (location (← get ctx (authorizeUrl "app") weak))
    "code").isSome
  let r ← get ctx (authorizeUrl "vault") weak
  let page ← get ctx (location r) weak
  check "where the sign-in page steps the session up"
    (containsStr page.bodyText "data-mode=\"stepup\"" &&
      containsStr page.bodyText "data-acr=\"phr\"")
  let r ← get ctx (authorizeUrl "vault" [("prompt", "none")]) weak
  checkEq "under prompt=none: interaction_required" (param (location r) "error")
    (some "interaction_required")
  -- acr_values: in order of preference, with aliases, unknown values ignored.
  for (values, want) in [("gold phr", "phr"), ("phrh phr", "phr"), ("phr phrh", "phr"),
      ("https://refeds.org/profile/mfa/phr", "phr"), ("phrh", "phrh")] do
    let r ← get ctx (authorizeUrl "app" [("acr_values", values)]) weak
    checkEq s!"acr_values={values} sends an mfa session to sign in for {want}"
      (param (location r) "acr") (some want)
  for values in ["mfa", "https://refeds.org/profile/mfa", "gold", "phr mfa",
      "https://refeds.org/profile/sfa"] do
    let r ← get ctx (authorizeUrl "app" [("acr_values", values)]) weak
    check s!"acr_values={values} is met by an mfa session" (param (location r) "code").isSome
  let code ← obtainCode ctx weak "app" [("acr_values", "mfa")]
  checkEq "whose ID token states its own level"
    (claimStr (← idClaims ctx (← exchange ctx code secret)) "acr")
    (some "https://refeds.org/profile/mfa")
  -- A passkey session: phrh, and the account now reaches phrh.
  let cookie ← signedIn ctx alice
  let code ← obtainCode ctx cookie "vault" [("acr_values", "https://refeds.org/profile/mfa")]
  let t ← exchange ctx code vaultSecret (client := "vault")
  let claims ← idClaims ctx t
  checkEq "the ID token states the session's level, above what was asked"
    (claimStr claims "acr") (some "phrh")
  checkEq "and the account's" (claimStr claims "pyle_account_acr") (some "phrh")
  let access := (jsonStr t "access_token").getD ""
  let roots ← Token.publishedRoots ctx.store
  checkEq "the access token states both"
    ((Token.verify roots "vault" (← ctx.clock) access).toOption.map fun i => (i.acr, i.accountAcr))
    (some (some "phrh", some "phrh"))
  let u ← get ctx "/userinfo" (headers := [("Authorization", s!"Bearer {access}")])
  checkEq "and /userinfo the account's" (jsonStr u "pyle_account_acr") (some "phrh")
  -- The claims parameter.
  let essential (vs : List String) : String :=
    (Json.mkObj [("id_token", Json.mkObj [("acr", Json.mkObj [("essential", Json.bool true),
      ("values", Json.arr (vs.map Json.str).toArray)])])]).compress
  let code ← obtainCode ctx cookie "app"
    [("claims", essential ["https://refeds.org/profile/mfa", "phr"])]
  let t ← exchange ctx code secret
  checkEq "an essential acr is answered with the first value the session meets"
    (claimStr (← idClaims ctx t) "acr") (some "https://refeds.org/profile/mfa")
  let refreshed ← postForm ctx "/token"
    [("grant_type", "refresh_token"), ("refresh_token", (jsonStr t "refresh_token").getD "")]
    (basic "app" secret)
  checkEq "and still after a refresh" (claimStr (← idClaims ctx refreshed) "acr")
    (some "https://refeds.org/profile/mfa")
  let r ← get ctx (authorizeUrl "app" [("claims", essential ["phrh"])]) weak
  checkEq "an essential phrh sends an mfa session to sign in" (param (location r) "acr")
    (some "phrh")
  let r ← get ctx (authorizeUrl "app" [("claims", essential ["gold"])]) cookie
  checkEq "an essential acr pyle does not know is refused" (param (location r) "error")
    (some "unmet_authentication_requirements")
  let voluntary := (Json.mkObj [("id_token", Json.mkObj [("acr", Json.mkObj
    [("values", Json.arr #["phr"])])])]).compress
  let r ← get ctx (authorizeUrl "app" [("claims", voluntary), ("acr_values", "mfa")]) weak
  checkEq "the claims parameter takes the place of acr_values" (param (location r) "acr")
    (some "phr")
  let r ← get ctx (authorizeUrl "app" [("claims", "not json")]) cookie
  checkEq "a malformed claims parameter is refused" (param (location r) "error")
    (some "invalid_request")
  let r ← get ctx (authorizeUrl "app" [("claims", "{\"userinfo\":{}}")]) weak
  check "one that says nothing about acr changes nothing" (param (location r) "code").isSome
  -- prompt=none.
  let r ← get ctx (authorizeUrl "app" [("prompt", "none"), ("acr_values", "phr")]) weak
  checkEq "prompt=none with too low a level: interaction_required" (param (location r) "error")
    (some "interaction_required")
  let r ← get ctx (authorizeUrl "app" [("prompt", "none"), ("acr_values", "phr")]) cookie
  check "and with a level that is high enough, a code" (param (location r) "code").isSome

/-- The levels as functions: the order, reading identifiers and the `amr`. -/
def acrTests : IO Unit := do
  group "assurance: levels"
  checkEq "lowest first" (Acr.all.map (·.rank)) [0, 1, 2]
  for a in Acr.all do
    check s!"{a} is read back" (Acr.ofIdentifier? a.identifier == some a)
    check s!"{a.shortName} is read back" (Acr.ofIdentifier? a.shortName == some a)
    for b in Acr.all do
      check s!"{a} satisfies {b} exactly when it is at least as strong"
        (a.satisfies b == decide (b.rank ≤ a.rank))
  checkEq "the bare mfa is an alias" (Acr.ofIdentifier? "mfa") (some .mfa)
  checkEq "REFEDS phishing-resistant MFA is phr"
    (Acr.ofIdentifier? "https://refeds.org/profile/mfa/phr") (some .phr)
  checkEq "REFEDS SFA is not a level"
    (Acr.ofIdentifier? "https://refeds.org/profile/sfa", Acr.ofIdentifier? "sfa") (none, none)
  checkEq "an unknown value is none" (Acr.ofIdentifier? "gold") none
  checkEq "the weakest value named"
    ((acrValuesRequest "phrh gold https://refeds.org/profile/mfa").level) (some .mfa)
  checkEq "no value named" (acrValuesRequest "gold").level none
  checkEq "an essential claim answers in the order given"
    ({ values := [("phrh", .phrh), ("phr", .phr)], essential := true : AcrRequest }.claim .phr)
    (some "phr")
  checkEq "a voluntary one does not"
    ({ values := [("phr", .phr)] : AcrRequest }.claim .phrh) none
  checkEq "a single factor of any kind reaches no level"
    ([({ password := true } : Acr.Capabilities), { webauthn := true }, { totp := true },
      { recovery := true }].map (·.level)) [none, none, none, none]

/-- The account page says how well a passkey account is protected. -/
def accountSafetyTests : IO Unit := withCtx fun ctx _ => do
  group "assurance: the account page"
  let ray ← ctx.store.addUser "ray" [] 1
  let (rid, _) ← sessionFor ctx ray
  let page ← getPage ctx "/account" (some rid)
  check "says a device-bound passkey account is well protected"
    (containsStr page.bodyText "<p id=\"safety\">This account can sign in with a security key \
      that verifies you and keeps its key on the device")
  let sam ← ctx.store.addUser "sam" [] 1
  let weak ← weakFor ctx sam
  let page ← getPage ctx "/account" (some weak)
  check "and asks an account without a passkey for one"
    (containsStr page.bodyText "<p id=\"safety\" class=\"notice\">This account signs in \
      with two factors, but has no passkey")

/-- The device grant still needs `phr`, and its tokens state the level. -/
def deviceAssuranceTests : IO Unit := withCtx fun ctx clock => do
  group "assurance: the device grant"
  let alice ← ctx.store.addUser "alice" [] 1
  discard <| addClients ctx
  let r ← deviceCodes ctx
  let deviceCode := (jsonStr r "device_code").getD ""
  let userCode := (jsonStr r "user_code").getD ""
  let page := s!"/device?{queryString [("user_code", userCode)]}"
  let weak ← weakFor ctx alice
  checkEq "an mfa session is sent to sign in for phr"
    (param (location (← get ctx page weak)) "acr") (some "phr")
  let post ← postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some weak)
  check "which cannot approve either" ((location post).startsWith "/signin?")
  let cookie ← signedIn ctx alice
  discard <| postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some cookie)
  clock.modify (· + ctx.config.devicePollSeconds + 1)
  let t ← pollDevice ctx deviceCode
  let roots ← Token.publishedRoots ctx.store
  checkEq "the tokens state the approving session's level"
    ((Token.verify roots "cli" (← clock.get) ((jsonStr t "access_token").getD "")).toOption.map
      (·.acr)) (some (some "phrh"))
  checkEq "the ID token too" (claimStr (← idClaims ctx t) "acr") (some "phrh")

/-- Forward authentication: per-host minimums and the sign-in facts. -/
def forwardAuthAssuranceTests : IO Unit := withCtx fun ctx0 _ => do
  group "assurance: forward authentication"
  let base := withForwardAuth ctx0
  let ctx := { base with config := { base.config with
    forwardAuthHosts := base.config.forwardAuthHosts ++
      [("open.example.org", "allow if user($u);"),
       ("vault.example.org", "allow if amr(\"user\"), acr(\"phrh\");"),
       ("acct.example.org", "allow if account_acr(\"phrh\");")],
    forwardAuthMinAcr := [("vault.example.org", .phr)] } }
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let weak ← weakFor ctx alice
  let some openCookie ← forwardSignIn ctx weak "open.example.org" "/"
    | check "an mfa session reaches a plain-policy host" false
  checkEq "an mfa session reaches a plain-policy host, whose floor is mfa"
    (← askProxy ctx "open.example.org" "/" (cookies := [openCookie])).status.toCode 200
  let raised := { ctx with config := { ctx.config with
    forwardAuthMinAcr := [("open.example.org", .phr)] } }
  let r ← askProxy raised "open.example.org" "/x" (cookies := [openCookie])
  checkEq "a cookie whose session is below the host's minimum goes round the grant again"
    r.status.toCode 302
  check "to the grant" ((location r).startsWith s!"{issuer}/forward-auth/grant?")
  let r ← askProxy raised "open.example.org" "/x" "POST" (cookies := [openCookie])
  checkEq "and a POST is 401" r.status.toCode 401
  let weak ← weakFor ctx alice
  let begun ← askProxy ctx "vault.example.org" "/"
  let g ← get ctx ((location begun).drop issuer.length |>.toString) weak
  checkEq "a host whose minimum is phr sends an mfa session to sign in for phr"
    (param (location g) "acr") (some "phr")
  let cookie ← signedIn ctx alice
  let some vaultCookie ← forwardSignIn ctx cookie "vault.example.org" "/"
    | check "a passkey session reaches it" false
  checkEq "a policy over acr and amr lets a passkey session in"
    (← askProxy ctx "vault.example.org" "/" (cookies := [vaultCookie])).status.toCode 200
  let some acctCookie ← forwardSignIn ctx weak "acct.example.org" "/"
    | check "an mfa session of an account with a passkey reaches acct" false
  checkEq "account_acr is the account's, not the session's"
    (← askProxy ctx "acct.example.org" "/" (cookies := [acctCookie])).status.toCode 200
  let bob ← ctx.store.addUser "bob" [] 1
  let bobWeak ← weakFor ctx bob
  let g ← throughGrant ctx bobWeak "acct.example.org" "/"
  check "an account without one is refused" (forwardCookie g).isNone
  -- The configuration's two forms.
  let parse (hosts : String) := (Json.parse ("{\"issuer\":\"https://a.example\",\
    \"rpId\":\"a.example\",\"origins\":[\"https://a.example\"],\
    \"forwardAuthSecret\":\"0123456789abcdef\",\"forwardAuthHosts\":" ++ hosts ++ "}")).toOption
    |>.map (Config.ofJson · "/etc/pyle")
  match parse "{\"a.example\":\"allow if user($u);\",\
      \"b.example\":{\"policy\":\"allow if user($u);\",\"minAcr\":\"phr\"}}" with
  | some (.ok c) =>
    checkEq "both forms are read" (c.forwardAuthHosts.map (·.1)) ["a.example", "b.example"]
    check "with the minimum of the object form"
      (c.forwardAuthMinAcr == [("b.example", Acr.phr)])
  | _ => check "both forms are read" false
  for (bad, what) in [("{\"b.example\":{\"policy\":\"allow if user($u);\",\"minAcr\":\"gold\"}}",
        "an unknown level"),
      ("{\"b.example\":{\"minAcr\":\"phr\"}}", "an object without a policy"),
      ("{\"b.example\":{\"policy\":\"allow if user($u);\",\"min\":\"phr\"}}", "an unknown key"),
      ("{\"b.example\":7}", "a number")] do
    check s!"{what} is refused" (match parse bad with | some (.error _) => true | _ => false)

/-- Migration 5 brings an older database forward. -/
def migrationTests : IO Unit := IO.FS.withTempDir fun dir => do
  group "assurance: migration 5"
  let s ← Store.Store.openFile (dir / "old.db")
  s.run fun c => do
    discard <| Store.currentVersion c
    for m in Store.migrations.take 4 do
      for st in m.statements do discard <| Store.exec c st
      discard <| Store.exec c
        "INSERT INTO schema_version (version, description, applied) VALUES (?, ?, ?)"
        #[m.version, m.description, (1 : Nat)]
    discard <| Store.exec c "INSERT INTO users (handle, name, created) VALUES (x'01', 'old', 1)"
    discard <| Store.exec c
      "INSERT INTO clients (id, name, redirect_uris, scopes, created) \
        VALUES ('old', 'Old', '[]', '[]', 1)"
    discard <| Store.exec c
      "INSERT INTO webauthn_credentials (id, user_id, algorithm, public_key, sign_count, \
        backup_eligible, backup_state, aaguid, name, created) \
        VALUES (x'02', 1, -7, x'03', 0, 0, 0, x'00', 'old key', 1)"
    discard <| Store.exec c
      "INSERT INTO webauthn_credentials (id, user_id, algorithm, public_key, sign_count, \
        backup_eligible, backup_state, aaguid, name, created) \
        VALUES (x'04', 1, -7, x'05', 0, 0, 0, x'00', 'added later', 7)"
  checkEq "the database is at version 4" (← s.version) 4
  s.migrate 2
  checkEq "and is brought to 5" (← s.version) 5
  checkEq "an older client has the mfa floor" ((← s.clientSettings "old").map (·.minAcr))
    (some .mfa)
  checkEq "the credential the invitation made is taken to verify the user"
    ((← s.findCredential (ByteArray.mk #[2])).map (·.userVerified)) (some true)
  checkEq "one added later is not, until an assertion shows it does"
    ((← s.findCredential (ByteArray.mk #[4])).map (·.userVerified)) (some false)
  check "which raises the flag"
    ((← s.recordCredentialUse (ByteArray.mk #[4]) 0 1 false true 9) &&
      ((← s.findCredential (ByteArray.mk #[4])).map (·.userVerified)) == some true)
  for bad in ["gold", "https://refeds.org/profile/sfa"] do
    let refused ← try
        discard <| s.run fun c =>
          Store.exec c "UPDATE clients SET min_acr = ?" #[.text bad]
        pure false
      catch _ => pure true
    check s!"a minimum of {bad} is refused by the schema" refused

/-- Set a client's minimum level, keeping its other settings. -/
def setMinAcr (ctx : Ctx) (client : String) (a : Acr) : IO Unit := do
  let cs := (← ctx.store.clientSettings client).getD {}
  discard <| ctx.store.setClientSettings client { cs with minAcr := a }

/-- A kleis attestation needs `kleisMinAcr`. -/
def kleisAssuranceTests : IO Unit := withCtx fun ctx _ => do
  group "assurance: kleis attestations"
  let alice ← ctx.store.addUser "alice" [] 1
  let some agentSecret ← registerClient ctx.store "agent" "An agent" [appRedirect]
      ["openid", "kleis"] false {} 1
    | check "an agent client" false
  -- What is in the request does not matter: the level is checked first.
  let attest (c : Ctx) (headers : List (String × String)) (path : String)
      (cookie : Option String := none) :=
    postForm c path [("request", "x")] headers cookie
  let weak ← weakFor ctx alice
  let strict := { ctx with config := { ctx.config with kleisMinAcr := .phr } }
  let r ← attest strict sameOrigin "/kleis/attest/session" (some weak)
  checkEq "with kleisMinAcr phr, an mfa session gets no attestation"
    (r.status.toCode, jsonStr r "error") (403, some "insufficient_acr")
  let code ← obtainCode ctx weak "agent" (scope := "openid kleis")
  let access := (jsonStr (← exchange ctx code agentSecret (client := "agent")) "access_token"
    ).getD ""
  let r ← attest strict [("Authorization", s!"Bearer {access}")] "/kleis/attest"
  checkEq "nor does a token from one" (r.status.toCode, jsonStr r "error")
    (403, some "insufficient_acr")
  let r ← attest ctx sameOrigin "/kleis/attest/session" (some weak)
  checkEq "an mfa session passes the default" (jsonStr r "error") (some "invalid_request")
  let r ← attest ctx [("Authorization", s!"Bearer {access}")] "/kleis/attest"
  checkEq "and so does its token" (jsonStr r "error") (some "invalid_request")
  let old : Pyle.Token.Identity :=
    { (default : Pyle.Token.Identity) with user := "alice", amr := ["hwk", "otp", "mfa"] }
  check "a token from before levels is read by its amr" (Pyle.Token.tokenLevel old == some .mfa)
  check "and one whose amr is no level is no level"
    (Pyle.Token.tokenLevel { old with amr := ["pwd"] }).isNone
  let stated : Pyle.Token.Identity := { old with acr := some "phr" }
  check "a stated level is itself" (Pyle.Token.tokenLevel stated == some .phr)
  check "and a stated level pyle does not know is none"
    (Pyle.Token.tokenLevel { old with acr := some "gold" }).isNone
  let now ← ctx.clock
  let forged ← Pyle.Token.issue ctx.store ctx.rootKey
    { user := "alice", amr := ["hwk", "user"], acr := "gold", authTime := now, groups := [],
      client := "agent", audience := ["agent", Pyle.Token.pyleAudience],
      scopes := ["openid", "kleis"] } now (now + 600)
  let r ← attest ctx [("Authorization", s!"Bearer {forged}")] "/kleis/attest"
  checkEq "a token stating an unknown acr gets no attestation"
    (r.status.toCode, jsonStr r "error") (403, some "insufficient_acr")
  let parse (extra : String) := (Json.parse ("{\"issuer\":\"https://a.example\",\
    \"rpId\":\"a.example\",\"origins\":[\"https://a.example\"]" ++ extra ++ "}")).toOption
    |>.map (Config.ofJson · "/etc/pyle")
  match parse "", parse ",\"kleisMinAcr\":\"phr\"", parse ",\"kleisMinAcr\":\"gold\"" with
  | some (.ok d), some (.ok c), some (.error _) =>
    check "kleisMinAcr is mfa by default, and read as a level" (d.kleisMinAcr == .mfa &&
      c.kleisMinAcr == .phr)
  | _, _, _ => check "kleisMinAcr is mfa by default, and read as a level" false

/-- The device grant answers to the client's minimum. -/
def deviceMinimumTests : IO Unit := withCtx fun ctx clock => do
  group "assurance: the device grant and the client's minimum"
  let alice ← ctx.store.addUser "alice" [] 1
  discard <| addClients ctx
  setMinAcr ctx "cli" .phrh
  let r ← deviceCodes ctx
  let userCode := (jsonStr r "user_code").getD ""
  let page := s!"/device?{queryString [("user_code", userCode)]}"
  let (synced, _) ← do
    let k ← SoftKey.new (backupEligible := true)
    enrol ctx alice k
    let some id := sessionCookieOf (← signInVia ctx k) | throw (.userError "no session")
    pure (id, k)
  checkEq "a phr session is sent to sign in for the client's phrh"
    (param (location (← get ctx page synced)) "acr") (some "phrh")
  let post ← postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some synced)
  checkEq "and cannot approve" (param (location post) "acr") (some "phrh")
  -- A minimum raised between approval and poll.
  setMinAcr ctx "cli" .mfa
  let r ← deviceCodes ctx
  let deviceCode := (jsonStr r "device_code").getD ""
  let userCode := (jsonStr r "user_code").getD ""
  let ok ← postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some synced)
  checkEq "a phr session approves for the phr floor" ok.status.toCode 200
  setMinAcr ctx "cli" .phrh
  clock.modify (· + ctx.config.devicePollSeconds + 1)
  checkEq "a poll after the minimum was raised gets nothing"
    (jsonStr (← pollDevice ctx deviceCode) "error") (some "invalid_grant")

/-- The token endpoint answers to the client's minimum as it is now. -/
def tokenMinimumTests : IO Unit := withCtx fun ctx _ => do
  group "assurance: the token endpoint and the client's minimum"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let weak ← weakFor ctx alice
  let code ← obtainCode ctx weak
  setMinAcr ctx "app" .phr
  let t ← exchange ctx code secret
  checkEq "a code whose sign-in is below the raised minimum is refused" (jsonStr t "error")
    (some "invalid_grant")
  setMinAcr ctx "app" .mfa
  let t ← exchange ctx (← obtainCode ctx weak) secret
  let rt := (jsonStr t "refresh_token").getD ""
  check "at the minimum, tokens" (jsonStr t "access_token").isSome
  setMinAcr ctx "app" .phr
  let refresh (token : String) := postForm ctx "/token"
    [("grant_type", "refresh_token"), ("refresh_token", token)] (basic "app" secret)
  checkEq "a refresh below the raised minimum is refused" (jsonStr (← refresh rt) "error")
    (some "invalid_grant")
  setMinAcr ctx "app" .mfa
  let fams ← ctx.store.run fun c =>
    Store.queryOne c "SELECT COUNT(*) FROM revoked_families" #[] (Store.colNat · 0)
  check "and its family is revoked" (fams.getD 0 ≥ 1)
  checkEq "for good, even with the minimum lowered again" (jsonStr (← refresh rt) "error")
    (some "invalid_grant")

/-- Second factors with a passkey are ignored, not checked. -/
def ignoredExtrasTests : IO Unit := withCtx fun ctx _ => do
  group "assurance: second factors with a passkey"
  let una ← ctx.store.addUser "una" [] 1
  discard <| giveTotp ctx una
  let k ← SoftKey.new
  enrol ctx una k
  let r ← signInVia ctx k (extra := [("totp", "000000"), ("recovery", "AAAAA-AAAAA")])
  checkEq "a passkey with a wrong code still signs in" r.status.toCode 200
  checkEq "and the code is not part of the sign-in"
    ((replyJson r).getObjValAs? (List String) "amr").toOption (some ["hwk", "user"])
  checkEq "nor counted against TOTP" ((← ctx.store.findTotp una.id).map (·.failures)) (some 0)

/-- Rows whose `amr` reads as no level fail closed: a session, a code, a
refresh token and a device approval that `Policy` could not have written. -/
def failClosedTests : IO Unit := withCtx fun ctx clock => do
  group "assurance: an amr that is no level is refused"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let now ← clock.get
  let id ← Crypto.randomBytes 32
  discard <| ctx.store.run fun c => Store.exec c
    "INSERT INTO sessions (id_hash, user_id, amr, factors, auth_time, created, last_seen, \
      client_address, user_agent) VALUES (?, ?, ?, '[]', ?, ?, ?, '', '')"
    #[.blob (Store.SecretHash.of id).bytes, .int alice.id.val, .text "[\"pwd\"]", .int now,
      .int now, .int now]
  let cookie := Session.encodeId id
  check "a session row whose amr is no level is no session"
    (← Session.current ctx (withCookie cookie)).isNone
  check "nor listed" (← Session.list ctx alice.id).isEmpty
  checkEq "so /authorize sends to sign in"
    ((location (← get ctx (authorizeUrl "app") cookie)).startsWith "/signin?") true
  -- A code.
  let code := "a-code-whose-amr-is-no-level"
  ctx.store.addCode (tokenHash code)
    { clientId := "app", redirectUri := appRedirect, codeChallenge := pkce.2, user := alice.id,
      scope := "openid", nonce := none, amr := ["pwd"], authTime := now,
      expires := now + 60 }
  checkEq "a code whose amr is no level is refused" (jsonStr (← exchange ctx code secret) "error")
    (some "invalid_grant")
  -- A refresh token.
  let rt := "a-refresh-token-whose-amr-is-no-level"
  ctx.store.startRefreshFamily (tokenHash rt)
    { family := ← Crypto.randomBytes 32, clientId := "app", user := alice.id,
      scope := "openid", amr := ["hwk"], authTime := now, expires := now + 3600 } now
  let r ← postForm ctx "/token" [("grant_type", "refresh_token"), ("refresh_token", rt)]
    (basic "app" secret)
  checkEq "a refresh token whose amr is no level is refused" (jsonStr r "error")
    (some "invalid_grant")
  -- A device approval.
  let d ← deviceCodes ctx
  let deviceCode := (jsonStr d "device_code").getD ""
  let userCode := (jsonStr d "user_code").getD ""
  discard <| ctx.store.decideDeviceCode (Device.normalise userCode |>.getD "")
    (.approved alice.id ["otp"] now) now
  clock.modify (· + ctx.config.devicePollSeconds + 1)
  checkEq "a device approval whose amr is no level is refused"
    (jsonStr (← pollDevice ctx deviceCode) "error") (some "invalid_grant")

/-- The assurance tests. -/
def assuranceTests : IO Unit := do
  failClosedTests
  kleisAssuranceTests
  deviceMinimumTests
  tokenMinimumTests
  ignoredExtrasTests
  acrTests
  migrationTests
  oidcAssuranceTests
  accountSafetyTests
  deviceAssuranceTests
  forwardAuthAssuranceTests

end PyleTests