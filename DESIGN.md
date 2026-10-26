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
| Passkey (discoverable WebAuthn credential, user verification) | primary, alone sufficient | Phishing-resistant: bound to the origin by the browser. |
| Security key (WebAuthn, possibly non-discoverable) | primary with UV, or second factor | Same ceremony, different flags. |
| TOTP (RFC 6238) | second factor only | SHA-1, 30 s, 6 digits by default: what every authenticator app supports. |
| Recovery codes | last resort | Ten single-use codes, stored hashed, shown once. |
| Password | optional first factor, never alone | Off by default.  Argon2id.  Exists for devices with no platform authenticator. |

A sign-in yields an **authentication method reference** (`amr`, RFC 8176):
`hwk`/`swk` with `user` for WebAuthn, `otp` for TOTP, `pwd` for a password.  It
is carried into every token (§5), so a service can demand a phishing-resistant
sign-in for something sensitive without trusting a boolean that only means
"some second factor happened".

**Assurance policy.**  A session is *strong* if it was established by a WebAuthn
assertion with user verification, or by any two distinct factors.  Only strong
sessions get tokens.  A password alone produces no session at all — it is only
a step.

**At least two.**  A user cannot remove their second-to-last authenticator, and
is nagged until they have registered two.  Losing a single key should never be
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
library, and reaches the page as a `data:` URL, which `img-src` allows.  A code is accepted for the current time
step and one step either side.  The step of the last accepted code is stored,
and a code for that step or an earlier one is refused: a code is good at most
once, which RFC 6238 recommends and most implementations forget.

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
- records `amr`, `auth_time` and the authenticators used.

**Step-up.**  A relying service may send `max_age` or ask for an `acr`; if the
session's `auth_time` is too old, or its factors too weak, pyle asks for a
fresh WebAuthn assertion without ending the session.  Removing an
authenticator, adding one and minting long-lived tokens always require a
step-up within the last five minutes.

A step-up need not be WebAuthn: two factors through the code form (a
password and a TOTP code, or a recovery code and another factor) are accepted
for account changes too, because recovery needs them — someone who has lost
every authenticator signs in with a recovery code and a second factor and must
then be able to register a new one.  The cost is that a real-time phisher who
relays both codes can register a passkey of their own.  §12 keeps this open.

Sessions are listed to their user, with the device and the time last used, and
can be ended individually.

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

ID tokens are JWTs, since that is what every OIDC client library expects.  Which
algorithm they are signed with is an open question (§12).

### 5.2 Biscuits for our own services

orchestra, taxis and diff-reviewer are ours, and they can do better than a JWT.
For them the access token is a **biscuit** whose authority block says:

```
user("christian");
amr("hwk"); amr("user");
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
decides access.

### 5.4 kleis

pyle signs a **third-party block** attesting `user("christian")` and the
`amr`, and appends it to a kleis biscuit.  A kleis grant can then say

```
check if user($u), ["christian"].contains($u) trusting ed25519/<pyle public key>;
```

which is the third-party-block question in kleis's §15, answered.  The flow for
handing an agent a kleis token becomes: sign in to pyle, ask kleis for a
token for a grant, and attenuate it — no owner typing a bearer name.

### 5.5 Command-line clients and agents

The taxis plugin, the diff-reviewer agent CLI and similar tools use the
**device authorization grant** (RFC 8628): the CLI shows a short code, the user
approves it in a browser with a passkey, and the CLI receives a biscuit.  This
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
moved to another row.  Signing keys rotate: the JWKS publishes the current key
and the previous one, and a biscuit root key rotation is announced to services
before it takes effect.

## 7. Abuse resistance

- **Enumeration.**  Discoverable passkeys mean sign-in starts without a
  username.  Where a username is asked for, the response does not depend on
  whether it exists.
- **Rate limits** per account and per client address, with exponential
  back-off, on every endpoint that checks a factor.  Five failed TOTP codes
  lock TOTP for that account for fifteen minutes; WebAuthn is not locked,
  since it cannot be guessed.
- **CSRF.**  `SameSite=Lax`, plus an `Origin` check on every state-changing
  request; the WebAuthn challenge is itself a CSRF token for the ceremony.
- **Clickjacking.**  `frame-ancestors 'none'`, and a strict CSP: the sign-in
  page needs no third-party script and gets none.
- **Audit.**  One append-only, hash-chained record per authentication event, in
  the same shape as kleis's §9.3: who, which factor, from where, outcome.
  Never a secret, a code or a challenge.

## 8. State

SQLite, one file, through `leansqlite`, which bundles the amalgamation.  (The
`db` package diff-reviewer and orchestra use does not build on the toolchain
`lean-biscuit` needs.)

| Table | Contents |
| --- | --- |
| `users` | id, handle (random 32 bytes, the WebAuthn user handle), name, groups |
| `webauthn_credentials` | credential id, user, COSE public key, sign count, flags, AAGUID, transports, name, created/last used |
| `totp` | user, encrypted secret, last accepted step |
| `recovery_codes` | user, HMAC, spent-at |
| `sessions` | id hash, user, amr, auth_time, created, last seen, client hints |
| `challenges` | challenge, purpose, user, expiry — deleted on first use |
| `clients` | OIDC clients: id, secret hash, redirect URIs, allowed scopes |
| `codes`, `refresh_tokens` | hashes only, with the binding fields of §5.1 |
| `keys` | encrypted signing keys, state (next/current/previous) |
| `audit` | §7 |

Session ids, codes and refresh tokens are stored as SHA-256 hashes, so reading
the database does not give anyone a session.

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
3. **No session without the policy.**  `Policy.establish` takes a
   `StrongAuthentication`, whose constructor is private to
   `Pyle.Session.Policy`, as is the constructor of the per-factor evidence it
   is built from and the SQL that writes a session row — a type-level
   guarantee in the style of kleis's `AuthorizedRequest`, not a theorem to
   maintain.
4. **Authorization codes.**  A token is issued for a code only if the code was
   issued to that client, for that redirect URI, with a challenge the verifier
   hashes to, and has not expired or been used.
5. **TOTP replay.**  Two accepted TOTP codes for the same user have strictly
   increasing time steps.
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
3. **No session without the policy**: structural, as above; `password_alone`,
   `totp_alone`, `recovery_alone` and the `ofFactors_*` theorems in
   `Session/Policy.lean` say what the policy rules out.
4. **Authorization codes**: `codeDecision_issue` — tokens are issued for a
   code only if the store handed back its row, it was issued to this client,
   for this `redirect_uri`, the verifier is well formed and its `S256`
   challenge is the code's, and it has not expired.  That it has not been
   used is part 2: `consumeCode` is a `take` on `codes`.
5. **TOTP replay**: `Totp.verify_increasing` and `Totp.verify_near`, in
   `Factor/Totp.lean`; the last accepted step is stored per user.
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
  Session/     Session, Policy (StrongAuthentication), StepUp
  Oidc/        Authorize, Token, Discovery, Jwks, Jwt, DeviceGrant
  Token/       Biscuit issuing, third-party attestation for kleis
  ForwardAuth.lean
  Store/       SQLite schema, migrations
  Crypto/      Ffi (sign, random, constant-time compare, Argon2id), Keys
  Http/        routes, cookies, CSRF, rate limiting
  Proofs/      Decisions, SingleUse, Cose: the theorems of §9 that need no private access
  Audit.lean
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
- **Replacing the root key, and ending every session.**  The root key never
  changes, and there is no way to end every session at once.  So the
  database together with the root key — a leaked backup, a stolen disk — is
  beyond repair from within pyle: with both, an attacker can make
  forward-authentication cookies for every live session and read every TOTP
  secret, and `keys rotate` changes neither.  Wanted: re-sealing the secret
  columns under a new root key, a new forward-auth MAC key with it, and a
  command that ends every session and refresh-token family.