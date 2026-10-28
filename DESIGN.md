# pyle

*πύλη, the gate.*  kleis is the key that opens one door for one purpose; the
pylē is where you are first asked who you are.

An identity provider, written in Lean 4 so that the parts of it a mistake would
be expensive in can be stated and proved.  People sign in to it once, with a
passkey or a security key, and the services behind it — orchestra, taxis,
diff-reviewer, and anything that speaks OpenID Connect — learn *who* is
asking without each of them keeping a password table.

pyle and kleis answer two different questions and are meant to be used
together:

| | asks | about |
| --- | --- | --- |
| **pyle** | who is this? | a person, or an agent acting for one |
| **kleis** | may this bearer spend that credential on this request? | a token held for an outside service |

kleis today takes the bearer's identity as given: an owner names it by hand in
`kleis token issue --bearer ci@build-07`.  pyle is where that name comes
from (§5.4).

## The parties

- The **user** holds authenticators: passkeys, security keys, an authenticator
  app.  They never hold a password that a service can see.
- A **relying service** (orchestra, taxis, diff-reviewer, Forgejo, Grafana)
  sends the user to pyle and gets back a statement about them, signed.
- A **reverse proxy** stands in for services that cannot do this themselves,
  asking pyle on every request whether the session is good (§5.3).
- **kleis** accepts tokens pyle has attested, so a grant can name a person
  rather than a string the owner typed.

```
 user (browser)            service                 pyle
   │  GET /                   │                        │
   ├─────────────────────────▶│                        │
   │  302 /authorize?…&code_challenge=…                │
   │◀─────────────────────────┤                        │
   ├──────────────────────────────────────────────────▶│  WebAuthn ceremony
   │◀──────────────────────────────────────────────────┤  session established
   │  302 service/callback?code=…&iss=…                │
   ├─────────────────────────▶│  POST /token (code, verifier)
   │                          ├───────────────────────▶│
   │                          │◀───────────────────────┤  id_token, access token
   │◀─────────────────────────┤  signed in             │
```

## What it replaces

Each service currently solves this on its own, and each in a different way:

- **taxis** signs people in with Google or GitHub OAuth, or a central
  password, and lets bots present personal access tokens.
- **diff-reviewer** has one password, which is also the bearer token for
  scripts, and no rate limit on `/api/login` — both called out in its README as
  things to fix before it posts under anyone's name.
- **orchestra** identifies people by GitHub login (`authorized_users`) and API
  clients by a static token in `clients/<name>.json`.
- **kleis** takes the bearer's name from whoever issues the token.

None of these has a second factor of its own, and none can say "this request
comes from an agent acting for Christian, on this one pull request".

## Non-goals

- **Not a public sign-up service.** Accounts are created by an administrator or
  by invitation.  Self-registration is a later question, not a v1 one.
- **No SMS or e-mail codes as factors.** Both are phishable and the second is
  only as strong as the mailbox.  E-mail is used to deliver invitations, never
  to sign in.
- **No SAML, no LDAP server** in v1.  Every service in scope speaks OIDC, or
  sits behind a proxy that can ask.
- **Not a password manager**, and not multi-tenant.
- **No implicit flow, no resource-owner password flow**, no tokens in URLs.
  These are deprecated by OAuth 2.1 for good reasons and supporting them would
  be the only reason to keep them.

## 1. Authenticators

| Kind | Role | Notes |
| --- | --- | --- |
| Passkey (discoverable WebAuthn credential, user verification) | primary, alone `phr` | Phishing-resistant: bound to the origin by the browser. |
| Security key (WebAuthn, possibly non-discoverable) | primary with UV (`phr`), or second factor | Same ceremony, different flags. |
| TOTP (RFC 6238) | second factor only | SHA-1, 30 s, 6 digits by default: what every authenticator app supports.  Up to five apps per account, together one authenticator and one kind of factor. |
| Recovery codes | last resort, second factor only | Ten single-use codes, stored hashed, shown once. |
| Password | optional first factor, never alone | Off by default.  Argon2id.  Exists for devices with no platform authenticator. |

A sign-in yields an **authentication method reference** (`amr`, RFC 8176):
`hwk`/`swk` with `user` for WebAuthn, `otp` for TOTP, `pwd` for a password,
the private `rec` for a recovery code, and `mfa` for two kinds.  OpenID
Connect EAP ACR Values 1.0 §3 adds `pop`, proof of possession of a key stored
who knows where; pyle always knows which of `hwk` and `swk` it is, and never
says `pop`.  The `amr` is carried into every token (§5), so a service can
demand a phishing-resistant sign-in for something sensitive without trusting
a boolean that only means "some second factor happened".

**Assurance policy.**  A session is *strong* if it was established by a WebAuthn
assertion with user verification, or by any two distinct factors.  Only strong
sessions exist.  A password alone, a security key without user verification
alone, a TOTP code alone or a recovery code alone produces no session at all —
each is only a step.

**Assurance levels.**  Every session records the level its sign-in reached,
its `acr`, and each service decides which it needs.  The levels are published
identifiers, lowest first:

| level | identifier | reached by |
| --- | --- | --- |
| `mfa` | `https://refeds.org/profile/mfa` (REFEDS MFA Profile) | two factors of distinct kinds |
| `phr` | `phr` (OpenID Connect EAP ACR Values 1.0 §2, "phishing-resistant") | a WebAuthn assertion with user verification |
| `phrh` | `phrh` (the same, "phishing-resistant hardware-protected") | the same from a credential that is not backup-eligible (the BE flag clear), whose key never leaves the authenticator |

Each level satisfies the ones below it, and the order is total.  There is no
single-factor level (§12 says why), so `mfa` is the floor of every comparison,
and REFEDS SFA's `https://refeds.org/profile/sfa` is a value pyle does not
know.  A service, a forward-auth host or kleis can be configured to need more
(§5); a request can raise the level it needs, never lower it: whoever controls
the browser controls the request.

Two definitions are a matter of reading.  `phr` asks that a party under the
relying party's control learn nothing that would let it authenticate as the
user elsewhere; WebAuthn's origin binding gives exactly that, and nothing else
pyle has does.  `phrh` asks that the information needed to authenticate be
held in a hardware-protected device; a credential that is not backup-eligible
is one the authenticator promises never to export, which is as close as
WebAuthn comes without attestation (§2.2, where an AAGUID allow-list makes it
closer).  So without `attestationRoots` and an allow-list, `phrh` rests on the
authenticator's own word about its backup-eligible flag.

Passwords are a deployment switch: turning `allowPasswords` off takes them
away as a factor, so an account that has no WebAuthn credential and relied on
a password with a TOTP or recovery code can no longer sign in, and needs a new
invitation.

**Account safety.**  What an account has registered bounds the level it can
reach: `phrh` or `phr` with a credential that has verified the user
(device-bound for `phrh`), `mfa` with two kinds of factor, and none with
fewer.  pyle states it to services as `pyle_account_acr` and `account_acr`
(§5), shows it on the account page in plain words, and asks for a passkey
until there is one.

**The account page.**  `/account` leads with that summary, then lists every
way in as one table grouped by kind — passkeys and security keys, whether
synced or kept on the key; authenticator apps; the password; how many
recovery codes are left — and then the sessions.  Adding happens on
`/account/add`, which registers a passkey (`residentKey` and user
verification required) or a security key (`residentKey` discouraged, user
verification preferred) itself, and sends an authenticator app, a password
and new recovery codes to a page each.

**At least two.**  A user cannot remove their second-to-last authenticator, and
is nagged until they have registered two.  Each WebAuthn credential counts
as one, and an account's authenticator apps count as one together.  A
removal is checked against what it leaves, in the transaction that makes it,
and rolled back if the factors left reach no level (two touch-only keys, say,
or apps alone) or are fewer than two authenticators; removing the password,
which is not counted, is checked only for the level.  Recovery codes do not
count towards that level: they are the last resort (§3), and each sign-in
spends one, so no removal may leave them as the only second factor.  The
account's own level, shown on its page and given to services, still counts
them.  Losing a single key should never be
an administrator's problem.

## 2. WebAuthn ceremonies

This is the part where a mistake costs the most, and the part best suited to
being stated precisely.  pyle implements the relying-party side of
WebAuthn Level 3 directly, rather than through a library, because the list of
checks *is* the specification of the security property.

### 2.1 Authentication (`navigator.credentials.get`)

Given a stored credential `c`, a pending challenge `ch` and the response, the
assertion is accepted only if all of the following hold:

1. the credential id is one registered to some user, and if `allowCredentials`
   was sent, it is one of those;
2. `userHandle`, when present, is that user's handle;
3. `clientDataJSON` parses, `type = "webauthn.get"`, `challenge = ch` (as
   base64url), and `origin` is one of the configured origins;
4. `crossOrigin` is absent or false, unless the deployment allows framing
   (it does not, by default);
5. `rpIdHash` in the authenticator data equals `SHA-256(rpId)`;
6. the user-present flag is set, and the user-verified flag is set if the
   policy requires it;
7. the backup-eligible flag has not changed since registration;
8. the signature verifies under `c.publicKey` over
   `authenticatorData ‖ SHA-256(clientDataJSON)`;
9. if either the stored or the received signature counter is non-zero, the
   received one is strictly greater — otherwise the credential is flagged as
   possibly cloned and the sign-in refused.

The challenge is consumed by the first attempt that names it, successful or not.

### 2.2 Registration (`navigator.credentials.create`)

The same checks for `type = "webauthn.create"`, plus: the attested-credential
flag is set; the algorithm is one we offered (`-7` ES256, `-8` EdDSA); the
credential id is not already registered to anyone; and the attestation
statement is one of the formats we accept.

**Attestation.**  The default is `none`: we do not ask authenticators to prove
their make.  `packed` self-attestation is checked when it is sent.  An
administrator may configure an AAGUID allow-list, in which case `packed` full
attestation is verified against the configured roots, the chain by OpenSSL
(§6.1).  An allow-list therefore admits only authenticators that attest: it
rules out synced platform passkeys, which send none.

### 2.3 What the ceremony needs

CBOR (RFC 8949, the deterministic subset WebAuthn uses), COSE keys (RFC 9052)
for EC2/P-256 and OKP/Ed25519, the authenticator-data layout, base64url, and
a JSON reader for `clientDataJSON`.  All of it parses untrusted bytes, so all
of it is written to be total and given round-trip properties (§9).

## 3. Second factors that are not WebAuthn

**TOTP.**  The secret is 20 random bytes, shown once as an `otpauth://` URI and
QR code, and stored encrypted (§6.3).  The QR code is encoded and rendered as
SVG in Lean (`Encoding/QrCode`, ISO/IEC 18004 in byte mode at level M) with no
library, and reaches the page as a `data:` URL, which `img-src` allows.  A code
is accepted for the current time step and one step either side.  The step of
the last accepted code is stored, and a code for that step or an earlier one is
refused: a code is good at most once, which RFC 6238 recommends and most
implementations forget.

An account may have several authenticator apps, each with its own name,
secret and last accepted step.  A submitted code is checked against each, in
one attempt, and counts for the first app it verifies for: it uses up that
app's step and no other's, since a code from one app says nothing about
another's secret.  The replay rule therefore holds per app — a code accepted
for an app is never accepted for it again — which is what an observer of the
code could exploit.  Failed codes and the lock of §7 are counted per account,
once per attempt, so more apps do not mean more guesses.  Two codes from two
apps are two factors of one kind and make no authentication: an account's
apps are often on the same phone.  An account has at most five apps,
which bounds the secrets one code is checked against; an app whose secret
does not open under the root key is left out of the check and audited, so
that one damaged row does not take TOTP away from the others.

**Recovery codes.**  Ten codes of 10 base32 characters, stored as
HMAC-SHA256 under a server key so a database leak is not a list of working
codes.  Using one marks it spent and prompts the user to register a new
authenticator.

**Passwords**, when enabled: Argon2id with parameters from RFC 9106's second
recommended option, compared through a constant-time primitive, and checked
against a breached-password list at the time it is set.

## 4. Sessions

A session is a row on the server and an opaque random identifier in a cookie:

- named `__Host-pyle`, so it is `Secure`, has `Path=/` and no `Domain`;
- `HttpOnly`, `SameSite=Lax`;
- the identifier is rotated on every change of authentication state, so a
  session fixed before sign-in is worthless after it;
- idle timeout (default 8 h) and absolute timeout (default 30 days);
- records `amr`, `auth_time` and the authenticators used; its level is read
  back from the `amr`, and is exactly the level of the authentication that
  wrote it (§9.1).

**Step-up.**  A relying service may send `max_age` or ask for an `acr`; if the
session's `auth_time` is too old, or its level too low, pyle sends the browser
to sign in again at the level needed, without ending the session.  The sign-in
page offers only what reaches that level and the endpoints refuse what falls
short, so the round trip cannot loop.  A step-up replaces the session's level
with the new authentication's, as it replaces `auth_time`: it says how the user
signed in just now.

**Account changes.**  Removing an authenticator, adding one and minting
long-lived tokens always require a step-up within the last five minutes; every
session is at least `mfa`, so a change needs two factors or a passkey, as
REFEDS MFA §3.2's factor independence asks.

A step-up need not be WebAuthn: two factors through the code form (a
password and a TOTP code, or a recovery code and another factor) are accepted
for account changes too, because recovery needs them — someone who has lost
every authenticator signs in with a recovery code and a second factor and must
then be able to register a new one.  The cost is that a real-time phisher who
relays both codes can register a passkey of their own.  §12 keeps this open.

Sessions are listed to their user, with the device and the time last used, and
can be ended individually.

**Ending access from outside.**  An administrator ends one account's access,
or everyone's, with `pyle sessions revoke`: in one transaction the sessions
are deleted, every refresh-token family the account holds is revoked —
those tied to a session (which ending the session revokes anyway) and those
that are not, from `offline_access` and the device grant — and the codes not
yet redeemed are withdrawn: authorization codes, approved device codes (the
device is then told `access_denied`) and forward-authentication codes.  What
it cannot reach are access tokens already issued, which services verify
offline and which live until they expire.  `pyle user disable` does the same
and marks the account disabled, which every way in checks again for itself —
sign-in by each method, a session's lookup, the token endpoint for codes,
refresh tokens and the device grant, `/userinfo` and the kleis attestation —
so a token that survived, say in a restored backup, is refused all the same.
`pyle user remove` ends the account's access and then deletes it, the rest
going with it by `ON DELETE CASCADE`, and so do the pending invitations for
its name or its address, which would otherwise make an account that services
keying accounts by either take for the removed one.  Access tokens state the
account's subject (its user handle, never reused) besides its name, and
`/userinfo` answers only for the account with that subject; a token from
before they did is answered only for an account that existed at its
sign-in.

None of this reaches a relying party's own sessions: pyle cannot end a
session Zulip keeps of its own, and says so each time.  Deactivating the
user there is the administrator's part, as is retiring the account in each
service before its address is given to anyone else.

**Administration in a browser.**  The same changes, except replacing the
root key and ending every session at once, can be made from pages under
`/admin` by an enabled member of the configured `adminGroup`.  The rule is
one function, `Admin.rule`: anyone else is answered `404` on every path under
`/admin`, before routing, so that no `405`, `Origin` refusal or redirect
says the interface is there; an administrator's session must be at `phr`,
and a weaker one is sent round the step-up of above at `phr` rather than
refused; and every change also needs a sign-in within the step-up window,
as an account change does (`Admin.rule_allow`).  Changes are JSON posts
under the `Origin` check and the rate limiter; pages change nothing.  The
last enabled administrator cannot be disabled, removed or taken out of the
group, checked in the transaction that makes the change; the command line is
not held to it, since it is how a deployment without administrators gets one
back.  An administrator's change is audited with the administrator as the
entry's account and what was changed at the start of its detail.  A
client's secret and an invitation's link are shown once, in the answer that
made them; the pages name pending invitations by the hash of their token.

## 5. What services receive

### 5.1 OpenID Connect

pyle is an OpenID Provider for the authorization-code flow, and only that:

- PKCE with `S256` is required for every client, confidential or not;
- redirect URIs are compared exactly, byte for byte;
- the authorization response carries `iss` (RFC 9207), so a client talking to
  more than one provider cannot be confused about which one answered;
- codes are single-use, expire in 60 s, and are bound to the client, the
  redirect URI and the code challenge;
- refresh tokens rotate on every use, and reusing an old one revokes the whole
  family;
- discovery (`/.well-known/openid-configuration`), JWKS, `userinfo`, and
  RP-initiated logout.

**Claims about the user.**  The ID token and `userinfo` release the same
claims for the same scope: `profile` gives `name` — the account's display
name, or its account name if it has none — and `preferred_username`, always
the account name; `email` gives `email` and `email_verified` for an account
with an address, and neither for one without; `groups` gives `groups`.
`email_verified` is always `true`: addresses are set by an administrator
(`pyle user add`/`user set --email`, or an invitation), never by the user,
and pyle sends no mail, so "verified" means vouched for by whoever runs pyle.
Two accounts cannot share an address, compared ignoring case, so a service
that matches accounts by `email` cannot be handed someone else's; addresses
are printable ASCII, since pyle folds ASCII case only and services fold
Unicode case.  Moving an address between accounts does hand one account
another's identity in such services, so the audit log records every change
with the old and the new address.  Display names refuse control and format
characters (bidirectional and zero-width controls), line separators and
non-ASCII spaces.  `email` is
not among a client's default scopes; it is granted only to clients registered
with it.

ID tokens are JWTs, since that is what every OIDC client library expects.  Which
algorithm they are signed with is an open question (§12).

**Levels.**  Each client has a minimum level (`pyle client add --min-acr`,
`mfa` unless set), and a request may ask for more with `acr_values` — a list
in order of preference, of which pyle reads the four identifiers, the bare
`mfa` of earlier versions, and REFEDS MFA 2.0's
`https://refeds.org/profile/mfa/phr` as `phr` — or with the `claims`
parameter's `id_token.acr` (OpenID Connect Core §5.5).  Any listed level will
do, so the session must reach the weakest listed and the client's minimum;
unknown values are ignored, as `acr_values` is voluntary.  A session below that
is sent to sign in again at the level needed; under `prompt=none` the client
gets `interaction_required` (and `login_required` without a fresh enough
session).  The ID token's `acr` is the session's level, except when `claims`
marks `acr` essential: then it is the first requested value the session meets,
as Core §5.5.1.1 requires and as REFEDS MFA §4.2.2.1 asks of an OP that
performed more than was requested, and a request none of whose values pyle
knows is refused with `unmet_authentication_requirements`.  The token
endpoint checks the client's minimum again, as it stands then, for a code and
for every refresh: a grant below it is refused, and a refresh-token family
below it revoked, so raising a client's minimum takes effect on its existing
grants too.  `amr` stays RFC
8176's, and `pyle_account_acr` names the account's strongest level, in the ID
token and at `userinfo`.

### 5.2 Biscuits for our own services

orchestra, taxis and diff-reviewer are ours, and they can do better than a JWT.
For them the access token is a **biscuit** whose authority block says:

```
user("christian");
amr("hwk"); amr("user");
acr("phrh");
account_acr("phrh");
auth_time(2026-10-25T10:00:00Z);
check if time($t), $t < 2026-10-25T11:00:00Z;
check if audience($a), ["taxis", "orchestra"].contains($a);
```

A service verifies it offline against pyle's root public key, without a
call back, and authorizes it with its own datalog policy.  And because a
biscuit can be attenuated by whoever holds it, the delegation the services
already want falls out without pyle knowing about it:

```
// orchestra, handing a task to an agent:
check if audience("diff-reviewer");
check if pull_request("chrisflav/kleis", 7);
check if time($t), $t < 2026-10-25T12:00:00Z;
```

The agent can act for the user on that one pull request for one hour, and
cannot widen it — the property kleis's §10.3 states for its own tokens holds
here for the same reason.

### 5.3 Forward authentication

For services that have no sign-in of their own, pyle answers Caddy's
`forward_auth`, Traefik's `forwardAuth` and nginx's `auth_request`:
`200` with `Remote-User` and `Remote-Groups` headers when the session cookie is
good and the user may reach that host, otherwise a redirect to sign in.  Which
users may reach which host is a datalog rule, like everything else that
decides access, over the user, the request and how the session signed in
(`acr`, `amr`, `account_acr`).  Each host has a minimum level, `mfa` unless
configured, which a session must reach before the rule is asked; one below it
is sent to sign in again at that level.

### 5.4 kleis

pyle signs a **third-party block** attesting `user("christian")`, the
`amr` and the `acr` — only for a sign-in at `kleisMinAcr` or better, `mfa`
unless configured, since existing grants trust the `user` fact as it is — and
appends it to a kleis biscuit.  A kleis grant can then say

```
check if user($u), ["christian"].contains($u) trusting ed25519/<pyle public key>;
```

which is the third-party-block question in kleis's §15, answered.  The flow for
handing an agent a kleis token becomes: sign in to pyle, ask kleis for a
token for a grant, and attenuate it — no owner typing a bearer name.

### 5.5 Command-line clients and agents

The taxis plugin, the diff-reviewer agent CLI and similar tools use the
**device authorization grant** (RFC 8628): the CLI shows a short code, the user
approves it in a browser with a passkey — the approval page needs `phr`, or
the client's minimum if higher, and the poll checks it again — and the CLI
receives a biscuit stating the approving session's level.  This
replaces personal access tokens pasted into config files, and those tokens get
an `amr` and an expiry like everything else.

## 6. Cryptography

### 6.1 Where each primitive comes from

| Primitive | Used for | Source |
| --- | --- | --- |
| SHA-256, SHA-512, HMAC-SHA256 | WebAuthn hashes, recovery codes, HKDF | `lean-crypto-hash` |
| SHA-1, HMAC-SHA1 | TOTP only | `lean-crypto-hash` for SHA-1; HMAC-SHA1 is a few lines here, or upstream |
| ES256, EdDSA **verification** | WebAuthn assertions | `lean-biscuit` (P-256, Ed25519) |
| Biscuit format and datalog | tokens, policies | `lean-biscuit` |
| ChaCha20-Poly1305 | encrypting TOTP secrets and signing keys at rest | FFI (OpenSSL): it handles the root key |
| X.509 chain validation | attestation roots, if configured | FFI (OpenSSL); the Lean side reads the AAGUID extension |
| **Signing** (ID tokens, biscuits) | everything we issue | FFI (OpenSSL), constant-time |
| Argon2id | passwords, if enabled | FFI (OpenSSL 3.2 and later) |
| Randomness | challenges, session ids, secrets | FFI (OpenSSL's DRBG, seeded by the OS) |
| HTTP | the server | `Std.Http`, from Lean itself |
| TLS | | terminated by the reverse proxy |

All of the FFI is one OpenSSL: the static `libcrypto` the Lean toolchain ships,
3.6 at the time of writing.  Nothing has to be installed where pyle runs.

### 6.2 Verification in Lean, signing outside it

The curve arithmetic in `lean-biscuit` is written over `Nat`, which is right for
a specification and for *verifying* signatures — every input is public — but
its running time depends on the scalar.  Using it to sign with pyle's
long-lived key would leak that key to anyone who can time enough signatures.

So the rule is: **secrets only meet code with a constant-time guarantee.**  The
Lean implementations stay as the specification, and a test checks that the FFI
signer's output verifies under the Lean verifier for every signature the test
suite produces.  The same point applies to kleis, which signs its biscuits with
`lean-biscuit` today.

Comparisons of secret values (session ids, recovery-code MACs, TOTP codes) go
through one FFI primitive as well; `lean-crypto-hash`'s no-early-exit
comparison is honest that Lean cannot promise constant time.

Three computations over secrets do run in Lean: HMAC-SHA1 for TOTP,
HMAC-SHA256 for recovery codes, and HKDF over the root key.  In
`lean-crypto-hash` these are fixed-schedule ARX and bitwise computations with
no secret-dependent branches or table lookups, but Lean promises nothing about
the timing of what it compiles them to, so this is a stated trade-off rather
than a guarantee.

### 6.3 Keys

A root key encrypts every secret column (TOTP secrets, signing keys) with
ChaCha20-Poly1305, with the row id as associated data so a secret cannot be
moved to another row.  A TOTP secret's associated data names both the user
and the app (`totp <user> <app>`), so it cannot be moved to another user or
to another of the same user's apps.  The single secret an account had before
migration 6 was sealed with the user id alone; that associated data is
accepted only for a row flagged `legacy_ad`, which only the migration sets,
and the first code such an app accepts re-seals it with the new associated
data and clears the flag.  Signing keys rotate: the JWKS publishes the
current key and the previous one, and a biscuit root key rotation is announced to services
before it takes effect.

Nothing uses the root key itself: each purpose derives its own key with HKDF
(`info` in brackets).  What depends on it, all of it:

| | how | when the root key is replaced |
| --- | --- | --- |
| signing keys, `keys.sealed`, retired ones too | sealed (`pyle signing-key v1`) | re-sealed: same key pair, `kid` and state |
| authenticator-app secrets, `totp_apps.secret` | sealed (`pyle totp v1`) | re-sealed for their row; `legacy_ad` cleared |
| recovery codes, `recovery_codes.digest` | HMAC (`pyle recovery-code v1`) | deleted: they cannot be recomputed |
| forward-authentication cookies | HMAC (`pyle forward-auth v1`) | stop verifying; the grant issues new ones |
| a secret being enrolled, held by the browser | sealed (`pyle totp v1`) | no longer opens; the enrolment begins again |
| an invitation's user handle, for a registration begun before migration 9 | HMAC (`pyle invitation-handle v1`) | recorded with the challenge since migration 9 |
| the padding credential ids of a named sign-in | HMAC (`pyle decoy-credential v1`) | change |
| the database's record of the key, `root_key` | HKDF (`pyle root-key fingerprint v1`) | replaced |

### 6.4 Replacing the root key

`pyle root-key rotate` exists for the day the root key may have leaked
together with a copy of the database.  The database records the fingerprint
of the key it is sealed under (migration 9; a database from before records
the key it is first opened with, once that key has been seen to open what
the database has sealed).  Every process that needs the key gets it through
one function, `RootKey.resolve`, which accepts the key file only if it
matches.

The rotation holds an exclusive `flock` on the key file's path with `.lock`
appended from its first step to its last.  With `new` standing for the
pending file — the key file's path with `.new-` and the new key's
fingerprint appended:

1. resolve the current key (finishing an interrupted rotation first);
2. in one `BEGIN IMMEDIATE` transaction, with `synchronous = FULL` so that
   the commit is on disk when it returns: check that the recorded fingerprint
   is the current key's; remove pending files left by rotations that never
   committed; write a fresh random key to `new` with `O_EXCL` and mode 0600
   and `fsync` it and its directory; re-seal every signing key and every app
   secret, opening each result under the new key before writing it, so that
   one that would not open aborts the whole transaction; delete the recovery
   codes; record the new fingerprint and the audit entry;
3. rename `new` over the key file, `fsync` the directory, and zero the old
   key's bytes through a descriptor opened before the rename (only if that
   file still held them).  The zeroing is best effort: a copy-on-write
   filesystem, an SSD or a snapshot may keep the old blocks, and a key file
   that is not writable is left alone with a warning.  Other copies of the old
   key are the operator's to destroy.

**Crash safety.**  The invariant is that one of the files holds the key the
database records, durably, at every moment:

- until the commit, the database records the old key and the key file holds
  it; a `new` left behind is ignored, and the next rotation removes it;
- from the commit until the rename, the database records the new key, which
  the pending file named by its fingerprint holds — its directory entry was
  synced before the commit — and `resolve`, at the next start or command or
  request, renames it over the key file as step 3 would have;
- after the rename, the key file holds the new key.

So no interruption loses the key, and no restart runs with a key the
database is not sealed under: a key file that matches neither, with no
pending file that does — the backup of one paired with the key of another —
is refused with an error that says so.

**Concurrency.**  Without the lock, a second rotation could finish the
first one's rename, write a pending file of its own, have the first one's
delayed rename install *that* key, and die before committing it: the
database would record one key and the file hold another.  With the lock,
rotations run one at a time, and a rename happens only under the lock,
after checking that the database records the pending key and that the key
file does not hold it already; and a pending file, being named by its key's
fingerprint, can only install that key.  `resolve` takes the lock only to
finish a rename; commands wait for it, the server does not — while a
rotation holds it, the server reads the pending key and uses it without
renaming anything, and the rotation installs it.  A process that dies
holding the lock releases it.

**A running server.**  The server keeps the key in memory, with its
fingerprint.  Before each request it reads the recorded fingerprint (one
indexed read) and, when it has changed, calls `resolve` again, which may
finish the rotation itself.  A request that took the old key just before
the commit may still try to seal with it; so every write that seals or keys
something under the root key — a signing key, an app's secret, recovery-code
digests — checks the recorded fingerprint inside its own transaction and
fails when it is not its key's.  SQLite's write lock orders that check
against the rotation's transaction: the write either commits first and is
re-sealed by the rotation, or comes after and fails.

What a rotation cannot do is undo a leak: the TOTP secrets and the signing
keys are the same as before, only sealed anew.  The remedy for a leaked
backup is therefore the rotation together with rotating the signing keys
until the leaked ones are retired, ending every session and refresh-token
family (`pyle sessions revoke --all`), and new authenticator apps.

## 7. Abuse resistance

- **Enumeration.**  Discoverable passkeys mean sign-in starts without a
  username.  Where a username is asked for, the response does not depend on
  whether it exists.
- **Rate limits** per account and per client address, with exponential
  back-off, on every endpoint that checks a factor.  Five failed TOTP codes
  lock TOTP for that account for fifteen minutes, however many authenticator
  apps it has; WebAuthn is not locked, since it cannot be guessed.
- **CSRF.**  `SameSite=Lax`, plus an `Origin` check on every state-changing
  request; the WebAuthn challenge is itself a CSRF token for the ceremony.
- **Clickjacking.**  `frame-ancestors 'none'`, and a strict CSP: the sign-in
  page needs no third-party script and gets none.
- **Audit.**  One append-only, hash-chained record per authentication event, in
  the same shape as kleis's §9.3: who, which factor, from where, outcome.
  Never a secret, a code or a challenge.
- **Administration.**  The pages under `/admin` answer `404` to everyone but an
  administrator at every path, so probing them learns nothing; they need a
  passkey session, and a fresh one for a change (§4).

## 8. State

SQLite, one file, through `leansqlite`, which bundles the amalgamation.  (The
`db` package diff-reviewer and orchestra use does not build on the toolchain
`lean-biscuit` needs.)

| Table | Contents |
| --- | --- |
| `users` | id, handle (random 32 bytes, the WebAuthn user handle), name, groups, email address (optional, unique ignoring case), display name (optional) |
| `invitations` | token hash, the account's name, groups, email address and display name, expiry |
| `webauthn_credentials` | credential id, user, COSE public key, sign count, flags (and whether it has verified the user), AAGUID, transports, name, created/last used |
| `totp_apps` | id (never reused), user, name, encrypted secret, last accepted step, created/last used, whether the secret still has the old associated data |
| `totp_lock` | user, failed codes, locked until |
| `recovery_codes` | user, HMAC, spent-at |
| `sessions` | id hash, user, amr, auth_time, created, last seen, client hints |
| `challenges` | challenge, purpose, user, expiry, for a registration the kind asked for and for an invitation's the user handle given — deleted on first use |
| `clients` | OIDC clients: id, secret hash, redirect URIs, allowed scopes, minimum level |
| `codes`, `refresh_tokens` | hashes only, with the binding fields of §5.1 |
| `keys` | encrypted signing keys, state (next/current/previous) |
| `root_key` | one row: the fingerprint of the root key the database is sealed under, never the key (§6.4) |
| `audit` | §7 |

Session ids, codes and refresh tokens are stored as SHA-256 hashes, so reading
the database does not give anyone a session.

The schema changes only by appended, numbered migrations (`Store/Schema`).
Migration 6 replaced the one-per-user `totp` table with `totp_apps` and
`totp_lock`: each account's secret became its first app, named
"Authenticator app", flagged as sealed with the old associated data (§6.3),
its last accepted step kept, and its failures and lock moved to the account.
Migration 7 records with a registration challenge the kind of authenticator
it was asked for.  Migration 8 adds the optional email address and display
name to `users` and `invitations`, with a unique index on `lower(email)`.
Migration 9 adds `root_key`, empty until the first process that holds the
key records it (§6.4), and the user handle of an invitation's challenge.

## 9. Properties worth verifying

As in kleis, the point of Lean is that some of these become theorems.

1. **Assertion soundness.**  `verifyAssertion` returns `ok` only if every check
   of §2.1 holds.  Stated as: `verifyAssertion c ch r = .ok u → Checks c ch r`,
   where `Checks` is the list written as a `Prop`, one conjunct per item.  The
   proof is mostly unfolding; the value is that the list is reviewable as a
   single definition.
2. **Single use.**  The challenge, code and refresh-token stores are state
   machines; a value that has been consumed is never accepted again.
   Invariant over every sequence of operations.
3. **No session without the policy.**  `Policy.establish` takes an
   `Authentication`, whose constructor is private to `Pyle.Session.Policy`, as
   is the constructor of the per-factor evidence it is built from and the SQL
   that writes a session row — a type-level guarantee in the style of kleis's
   `AuthorizedRequest`, not a theorem to maintain.  Its level is computed from
   its factors, never supplied.
4. **Authorization codes.**  A token is issued for a code only if the code was
   issued to that client, for that redirect URI, with a challenge the verifier
   hashes to, and has not expired or been used.
5. **TOTP replay.**  Two accepted TOTP codes for the same authenticator app
   have strictly increasing time steps.
6. **Attenuation.**  Inherited from biscuit: a block appended by a service or
   an agent never widens what the token permits.
7. **Parsers.**  CBOR, COSE and base64url are total, and encode-then-decode is
   the identity on well-formed values.

1, 3 and 7 are design constraints from the first commit; 2, 4 and 5 are the
theorems worth proving; 6 is inherited.

### 9.1 What is proved

Every theorem below uses no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`, and none uses `sorry` or `native_decide`.

1. **Assertion soundness**: `verifyAssertion_sound` against `AssertionChecks`,
   in `WebAuthn/Assertion.lean`.  **Registration soundness** likewise:
   `verifyRegistration_sound` against `RegistrationChecks`, one conjunct per
   item of §2.2 numbered as the steps of WebAuthn L3 §7.1 (7–10, with 11
   folded into 10, 13–17, 20–22 and 25), in `WebAuthn/Registration.lean`.
   Steps 17 (backup state only with backup eligibility) and 25 (credential id
   at most 1023 bytes) are enforced by `AuthenticatorData.parse` and proved
   from it (`parse_backup`, `parse_credentialId`); `AssertionChecks` carries
   the backup-flag check too.  Step 22 is the implementation's own
   `verifyAttestation` call, written down, and step 21 follows from it.  Not
   in the theorem: 12 (the hash is computed), 18 and 19 (the backup flags are
   reported for policy), 23 and 24 (the attestation policy, the caller's),
   26 (the credential id is not already registered, which needs the store
   and is the caller's), and 28 (extensions, not acted on).

   What the challenge conjunct is worth: both theorems take the challenge as
   a parameter, and the server takes it from the same client data
   (`Policy.challengeOf`), so the conjunct says only that the client data
   names it in canonical base64url.  That the ceremony answers a challenge
   the server issued, for this purpose, unexpired and not used before, comes
   from the caller: `Policy.checkAssertion` and
   `SignIn.consumeRegistrationChallenge` go on only when
   `Store.consumeChallenge` hands back a row, which part 2 covers.
2. **Single use**, in two parts.
   * *The decisions.*  Each table hands the row it deleted or read to a pure
     function, and the store or handler only carries out what that function
     returns: `Store.challengeDecision` (in `Store.consumeChallenge`),
     `Oidc.codeDecision` (in `Oidc.codeGrant`), `Store.refreshDecision` (in
     `Store.rotateRefreshToken`) and `Store.deviceDecision` (in
     `Store.pollDeviceCodeFor`).  `Proofs/Decisions.lean`: a row the store did
     not hand back is refused (`challengeDecision_none`, `codeDecision_none`,
     `deviceDecision_none`); a refresh token is rotated only if it is the
     client's, unused, unexpired and of an unrevoked family
     (`refreshDecision_rotate`, `refreshDecision_revoked`); a used one revokes
     its family and is never rotated (`refreshDecision_reused`); another
     client's changes nothing (`refreshDecision_otherClient`,
     `deviceDecision_otherClient`); a device code yields tokens only for its
     client, unexpired, once approved, for the approving user
     (`deviceDecision_approved`, `deviceDecision_collect`); a challenge comes
     back only for its purpose, unexpired (`challengeDecision_some`), and a
     challenge issued to a user admits only that user's credential
     (`Challenge.admits_user`).
   * *The state machines.*  `Proofs/SingleUse.lean` models each consume-once
     table as `Table`, a finite map with `add`, `update`, `take` and `purge`,
     where `take` returns and removes a row: from the empty table no sequence
     of operations returns a key twice (`Table.run_nodup`,
     `Table.run_consumed`).  The refresh-token store is `Families`, whose
     rotation step calls `Store.refreshDecision` itself: no token is rotated
     twice (`Families.run_rotated_nodup`), presenting a used token revokes its
     family (`Families.step_reused`), and a revoked family stays revoked,
     never holds a token again, and is never rotated into
     (`Families.run_revoked`).
   * *Assumptions.*  The models are linked to the SQL, not derived from it.
     Each operation is atomic: one `DELETE … RETURNING` statement
     (`consumeChallenge`, `consumeCode`, `consumeForwardAuthCode`) or one
     `BEGIN IMMEDIATE` transaction (`pollDeviceCodeFor` and
     `redeemInvitation`, each a read and a conditional delete;
     `rotateRefreshToken`, `startRefreshFamily`, and the family revocations of
     `revokeRefreshFamily`, `revokeUserClientFamilies` and
     `addRefreshFamily`), under the store's lock.  An insert into a revoked
     family is refused by the trigger `refresh_tokens_not_revoked`
     (migration 1), the trigger `sessions_end_families` (migration 4) is one
     more family revocation, and nothing deletes from `revoked_families`.
     Values handed out never repeat: each is 32 random bytes — a challenge
     stored as it is, every other value as its SHA-256 — and the models
     refuse to add a key that has been added before.  The docstrings of
     `Table` and `Families` name the statements.
   * *A known gap.*  A code presented again revokes the refresh-token family
     its first exchange began (RFC 6749 §4.1.2), but that revocation
     (`Oidc.codeGrant`: `familyExists`, then `revokeRefreshFamily`) runs in
     transactions separate from the `consumeCode` of the first exchange and
     from its `startRefreshFamily`.  A replay that lands after the first
     exchange consumed the code and before it began the family finds no
     family and revokes nothing; the replay itself is still refused.  This
     predates the proofs, and nothing above claims otherwise.
3. **No session without the policy**: structural, as above.  The theorems
   of `Session/Policy.lean` say what each level needs and what the policy
   rules out:
   * the level a session records is the level its factors justify:
     `Authentication.level_eq_ofAmr` — the session keeps the `amr`, and
     `Acr.ofAmr` reads back exactly `Authentication.level`, the level computed
     from the factors (`level`).  It holds because an authentication uses
     each kind of factor at most once.  `Acr.ofAmr` fails closed: an `amr` that
     shows neither a phishing-resistant factor nor two kinds (`mfa`) is no
     level, and a session, code, refresh token, device approval or access
     token carrying one is refused; so is an access token whose `acr` pyle
     does not know;
   * a password alone, a security key without user verification alone, a
     TOTP code alone and a recovery code alone are no authentication
     (`password_alone`, `key_alone`, `totp_alone`, `recovery_alone`, all from
     `ofFactors_single`: one factor that is not phishing-resistant), nor are
     two factors of one kind (`ofFactors_same_kind`) or of two users
     (`ofFactors_two_users`);
   * every authentication has a phishing-resistant factor or two kinds of
     factor (`strong`), and one at `mfa` has two kinds (`level_mfa`);
   * `phr` needs WebAuthn with user verification (`level_phr`), and `phrh` the
     same from a credential that is not backup-eligible (`level_phrh`);
   * in `Session/Acr.lean`, the order of the levels is a total order
     (`Acr.le_refl`, `le_trans`, `le_antisymm`, `le_total`), `satisfies` is
     monotone in both arguments (`Acr.satisfies_mono`), a request added to a
     floor never lowers it (`Acr.satisfies_max`), `mfa` is the least level
     (`Acr.mfa_le`), and REFEDS SFA is not a level (`Acr.ofIdentifier_sfa`).

   Not proved: that the endpoints ask for the right level.  `Authorize`,
   `ForwardAuth` and the device page compare the session's level with what
   they need through `Acr.satisfies`, and the theorems say what that
   comparison means; that each compares with the right minimum is checked by
   the tests.
4. **Authorization codes**: `codeDecision_issue` — tokens are issued for a
   code only if the store handed back its row, it was issued to this client,
   for this `redirect_uri`, the verifier is well formed and its `S256`
   challenge is the code's, and it has not expired.  That it has not been
   used is part 2: `consumeCode` is a `take` on `codes`.
5. **TOTP replay**: `Totp.verify_increasing` and `Totp.verify_near`, in
   `Factor/Totp.lean`; the last accepted step is stored per authenticator
   app.  Across an account's apps, `Policy.checkTotp` hands them to the pure
   `Totp.verifyAny`, of which `Pyle.Proofs.Decisions` proves that a code is
   accepted only for an app it verifies for, for a step after that app's
   last (`verifyAny_mem`, `verifyAny_increasing`, `verifyAny_near`), and
   that once the store records that step for the app no code at or before
   it is accepted for the app again, while the other apps are untouched
   (`verifyAny_acceptStep`, `acceptStep_other`).  Two codes from two apps
   are no authentication (`Policy.two_totp`).
6. **Attenuation**: inherited from `lean-biscuit`.
7. **Parsers**: base64url (`Base64Url.decode_encode`,
   `Base64Url.encode_decode`) and CBOR (`Cbor.decode_encode`, for well-formed
   items within the depth and size bounds) round-trip.  COSE, in
   `Proofs/Cose.lean`: the key an authenticator writes for a P-256 point on
   the curve is read back, through CBOR bytes, as that point compressed
   (`cose_roundTrip_es256`), and a stored Ed25519 key that decompresses is
   read back as itself (`cose_roundTrip_edDsa`).  A stored P-256 key cannot
   be written out again without the square root that recovers `y`, which pyle
   never computes, so that round trip starts from the coordinates.

8. **Administration**: `Admin.rule_allow` — the pages let a request through
   only for an administrator whose session is at `phr` or better, and a
   change only with a sign-in within the step-up window; `Admin.rule_hidden`
   — anyone else is shown nothing.  That the handlers ask `rule` is checked by
   the tests, not proved.

Not proved: anything about SQLite itself, the triggers or the lock — they are
the assumptions of part 2; the parsers' totality beyond being total Lean
functions; and the curve arithmetic (below).

Out of scope for proofs: constant-time behaviour (§6.2), TLS, the browser, and
the correctness of the curve arithmetic itself, which rests on test vectors
until someone proves it.

## 10. Module layout

```
Pyle/
  Encoding/    Base64Url, Cbor, Cose, Json, QrCode
  WebAuthn/    AuthenticatorData, ClientData, Assertion, Registration, Attestation
  Factor/      Totp, RecoveryCode, Password
  Session/     Session, Acr (the levels), Policy (Authentication), StepUp
  Oidc/        Authorize, Token, Discovery, Jwks, Jwt, DeviceGrant
  Token/       Biscuit issuing, third-party attestation for kleis
  ForwardAuth.lean
  Store/       SQLite schema, migrations
  Crypto/      Ffi (sign, random, constant-time compare, Argon2id), Keys
  Http/        routes, cookies, CSRF, rate limiting
  Proofs/      Decisions, SingleUse, Cose: the theorems of §9 that need no private access
  Audit.lean
  RootKey.lean reading the root key, and replacing it (§6.4)
  Admin.lean   ending access, disabling and removing accounts (§4)
  Admin/      the administration pages: who may (`rule`), endpoints, pages, script
web/           sign-in and account pages (no framework needed; a few hundred lines)
```

pyle does not depend on kleis: what it might have borrowed — HTTP, the AEAD,
X.509 — it takes from `Std.Http` and OpenSSL instead (§12).

## 11. Milestones

**M0 — the ceremony.**  Encoding, WebAuthn authentication and registration
over test vectors from the WebAuthn specification and from real authenticators
(captured once, checked in).  No server.  Theorem 1 and the parser properties.

**M1 — passkey-only provider.**  Server, sessions, OIDC authorization-code
flow with PKCE, discovery and JWKS, FFI signing.  diff-reviewer moves onto it
and loses its password-as-bearer-token.

**M2 — second factors.**  Security keys as a second factor, TOTP, recovery
codes, the two-authenticator rule, step-up.

**M3 — biscuits.**  Access tokens as biscuits; orchestra attenuates them for
agents; the device grant for CLIs; the kleis attestation of §5.4.  taxis moves
from Google/GitHub sign-in to pyle, and its personal access tokens become
device-grant biscuits.

**M4 — the rest.**  Forward auth, optional passwords, theorems 2, 4 and 5,
deployment.

## 12. Open questions

- **The ID-token signature algorithm.**  OIDC requires `RS256` to be available,
  and some clients support nothing else; `ES256` is widely supported;
  `EdDSA` is the nicest and the least supported.  Since signing goes through
  FFI anyway, offering `RS256` and `ES256` costs little — but RSA verification
  then has no Lean specification.  Leaning towards `ES256` by default, `RS256`
  per client when a client needs it.
- **Account recovery when every authenticator is lost.**  Recovery codes cover
  most of it.  Beyond them: an administrator re-invites, which is honest about
  being a human process.  Anything automatic is a way in for someone else.
- **A shared package.**  kleis and pyle overlap in the audit chain and in what
  they want from OpenSSL.  Decided for now: no shared package, and no
  dependency of pyle on kleis; the overlap is small, and `Std.Http` and OpenSSL
  cover the rest.  Revisit if the two FFI shims grow towards each other.
- **Upstream identity providers.**  Signing in *with* GitHub at pyle would
  make migrating taxis users easy and would make GitHub a way into everything.
  Leaning towards linking a GitHub account only to import a profile, never to
  sign in.
- **Step-up for adding authenticators.**  Whether adding an authenticator
  should require a WebAuthn step-up whenever the account still has a usable
  WebAuthn credential, so that relayed codes (§4) can no longer add one, at
  the price of a recovery path that must tell "lost every key" from "chose
  not to use it".
- **Synced passkeys.**  Passkeys synced by Apple, Google or a password manager
  are as strong as that account.  Whether to require device-bound credentials
  (backup-eligible flag clear) for administrators is a policy knob to decide.
  A service can already ask for it, as `phrh`; what is open is whether pyle
  should enforce it per group.
- **Single-factor accounts and sessions: considered and rejected.**  An
  `sfa` level — a password or a touch-only security key alone, accounts
  created with one, services opting down to it — was built and taken out
  again.  The trouble is enrolment: an account that may be managed with its
  one factor can use that factor to add a second and a passkey, and so mint
  `mfa` and `phrh` sessions from a stolen password (review finding H1).
  Requiring more for enrolment than for sign-in strands the account instead.
  So nothing is weaker than before levels: every session is strong.
- **The `acr` answered to `acr_values`.**  REFEDS MFA 2.0 §4.2.2.1 asks an OP
  that performed phishing-resistant MFA for a request of plain MFA to assert
  only `https://refeds.org/profile/mfa`.  pyle does so when the request is an
  essential `claims` request, which REFEDS §4.4 tells conforming relying
  parties to send, and otherwise states the session's own level, which tells a
  service more.  If REFEDS relying parties that use `acr_values` turn up, the
  voluntary request may have to be answered the same way.
- **What a leaked root key leaves behind.**  Replacing the root key (§6.4)
  and ending every session (§4) were open here and are done.  Still open:
  the TOTP secrets a leak gave away stay valid until each user replaces their
  apps, which pyle can only ask for; recovery codes are deleted by a rotation
  rather than carried over, since they cannot be re-keyed — the cost is that
  every account has to make new ones; and the padding credential ids of a
  named sign-in change with the key, so someone who asked for a name's
  allow-list before and after a rotation can tell its real credentials from
  the padding.