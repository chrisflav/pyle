# pyle

*πύλη, the gate.*  kleis is the key that opens one door for one purpose; the
pylē is where you are first asked who you are.

An identity provider.  People sign in once, with a passkey or a security key,
and the services behind it learn who is asking: through OpenID Connect, through
biscuit tokens they can verify offline and narrow for an agent, or through a
reverse proxy that asks on their behalf.

> [!WARNING]
> **Experimental, LLM-generated, and not reviewed by a human.**
>
> This code is being written by an LLM (Claude). No human has read it line by
> line. It is meant to decide who may sign in to things; read it before
> trusting it with anything you would mind someone else getting into.

See [DESIGN.md](DESIGN.md) for what it does and why it is built the way it is.

## Building

```sh
lake build    # the library and `pyle`
lake test     # the test suite
```

Needs OpenSSL headers (`libssl-dev`).  The library itself is the static one the
Lean toolchain ships, so the binary needs nothing installed where it runs.

## Usage

pyle reads one JSON configuration file, named by `--config`, by
`$PYLE_CONFIG`, or `pyle.json` in the current directory:

```json
{
  "issuer": "https://auth.example.org",
  "rpId": "auth.example.org",
  "origins": ["https://auth.example.org"],
  "database": "pyle.db",
  "rootKeyFile": "root.key"
}
```

Optional keys: `host` (default `127.0.0.1`), `port` (`8420`),
`sessionIdleSeconds` (eight hours), `sessionAbsoluteSeconds` (thirty days),
`trustedProxies` (peer addresses whose `X-Forwarded-For` is believed; none by
default), `allowPasswords` (`false`: whether users may add a password as one of
two factors), `attestationRoots` (DER or PEM files of trust anchors for
`packed` attestation; none) and `aaguidAllowList` (the authenticator models
that may be registered, as AAGUIDs; any by default — when set, it needs
`attestationRoots`, and only authenticators with a verified attestation chain
and a listed AAGUID can be registered — which rules out synced platform
passkeys, since those do not send attestation).  Relative paths are relative to the
configuration file.  Unknown keys are an error.

```sh
pyle init --config pyle.json        # create the root key (mode 0600) and the database
pyle serve --config pyle.json       # answer HTTP; put a TLS-terminating proxy in front
pyle user add alice --group admin   # create an account
pyle user list                      # list the accounts
pyle invite bob --group staff --ttl 7d   # print a link that creates bob's account
pyle audit verify                   # check the audit log's hash chain
pyle version
```

Keep a copy of the root key: the secrets sealed under it cannot be read
without it.

Every reply pyle makes carries its security headers (a strict CSP with
`frame-ancestors 'none'`, `nosniff`, `Referrer-Policy: no-referrer`, and
`Strict-Transport-Security` when the issuer is `https://`).  The exception is
the replies `Std.Http` makes on its own before a request reaches pyle — `400`
for a malformed request, `413` for an oversized body — which carry none of
them; have the reverse proxy add the headers if that matters.

### Signing in

Accounts are created by invitation: `pyle invite <name>` prints
`<issuer>/invite/<token>` (valid for seven days unless `--ttl` says otherwise;
only the token's hash is stored).  Whoever opens it creates the account's
first passkey, is told the account is ready, and signs in with it from there.

`/account` sums up in plain words how well the account is protected, and asks
for a passkey until it has one, for a second authenticator until it has two,
and for recovery codes when none are left.  Below that, one table lists every
way the account signs in, grouped by kind — passkeys and security keys (synced,
or kept on the key), authenticator apps, the password where `allowPasswords`
is set, and how many recovery codes are left — each with its rename and
remove buttons, and then the sessions, each of which can be ended.  "Add a
sign-in method" leads to `/account/add`, which offers a passkey (recommended),
a security key, an authenticator app, a password and new recovery codes; a
passkey or a security key is registered right there, the others have a page
each.  The last two authenticators cannot be removed.

An account can have several authenticator apps (TOTP), each with its own
secret and name, added, renamed and removed one by one.  Every app counts as
an authenticator towards the two an account keeps, but all of them together
are one kind of factor: two codes from two apps do not sign anyone in.  A code
counts for the app it came from, and is good once for that app; the lock after
five wrong codes is the account's, so more apps do not mean more guesses.

A session needs a passkey (WebAuthn with user verification) or two distinct
factors: a security key without user verification, a TOTP code, a recovery
code, a password.  A password, a security key without user verification or a
code alone never signs anyone in.  Adding or removing a way in needs a fresh
authentication within the last five minutes.

### Assurance levels

Every session records the level its sign-in reached.  Lowest first:

| level | `acr` | reached by |
| --- | --- | --- |
| mfa | `https://refeds.org/profile/mfa` ([REFEDS MFA](https://refeds.org/profile/mfa)) | two distinct factors: a security key, a TOTP code, a recovery code, a password |
| phr | `phr` ([OpenID Connect EAP ACR Values 1.0](https://openid.net/specs/openid-connect-eap-acr-values-1_0.html)) | a passkey: WebAuthn with user verification |
| phrh | `phrh` (the same) | a passkey or security key that verifies the user and is not backup-eligible, so its key never leaves the device |

Each level satisfies the ones below it, and `mfa` is the floor: there is no
single-factor level, and REFEDS SFA (`https://refeds.org/profile/sfa`) is a
value pyle does not know.  A service can ask for more — registered for it
(`--min-acr`, or `minAcr` for a forward-auth host), or per request — never
for less.
When the session falls short, pyle sends the browser to sign in again at the
level needed, without ending the session.

Two caveats.  `phrh` rests on the authenticator's own backup-eligible flag:
without `attestationRoots` and an `aaguidAllowList`, nothing proves that the
key really is held in hardware, only that the authenticator says it will not
be synced.  And turning `allowPasswords` off takes the password away as a
factor: an account that signed in with a password and one code, and has no
passkey or security key, can no longer sign in, and needs a new invitation.
Check `pyle user list` (accounts with no authenticators) before switching
passwords off.

Pages, served with no third-party code under a strict CSP:

| | |
| --- | --- |
| `GET /signin?return=<path>[&max_age=<s>][&acr=<level>]` | sign in, or step up the current session, at `level` (`mfa`, `phr`, `phrh`, or an identifier) or better; then `303` to `return`, which must be a path on this origin |
| `GET /account` | the account: its protection, how it signs in, its sessions |
| `GET /account/add` | choose a way to sign in to add; registers a passkey or a security key |
| `GET /account/add/app` | add an authenticator app: name it, scan the QR code or type the key, confirm with a code |
| `GET /account/add/password` | set or change the password, if `allowPasswords` is set |
| `GET /account/add/recovery-codes` | make new recovery codes and show them once |
| `GET /invite/<token>` | register an invited account's first passkey |
| `GET /assets/pyle.js`, `GET /assets/pyle.css` | the pages' script and stylesheet |

The JSON endpoints behind them (`POST`, `Origin` checked, binary values in
base64url):

| | body | answer |
| --- | --- | --- |
| `/signin/webauthn/begin` | `{}` (passkey) or `{"name"}` (security key) | WebAuthn request options |
| `/signin/webauthn/finish` | `{"credential", "totp"?, "recovery"?, "password"?, "return"?, "acr"?}` (second factors are ignored with a passkey that verified the user) | `{"redirect", "amr", "acr"}` and the session cookie |
| `/signin/stepup/begin`, `/signin/stepup/finish` | as above, for the current session | as above |
| `/signin/codes` | `{"name"}` and two of `"password"`, `"totp"`, `"recovery"`; `"return"`?, `"acr"`? | as above |
| `/invite/<token>/begin`, `/invite/<token>/finish` | `{}`; `{"credential", "name"?}` | creation options; `201 {"name"}` |
| `/account/authenticators/register/begin`, `…/finish` | `{"kind"?}`; `{"credential", "name"?, "kind"?}` (`kind` is `passkey`: discoverable, user verification required; or `security-key`: neither required) | creation options; `201 {"id"}` |
| `/account/authenticators/rename`, `…/remove` | `{"id", "name"}`; `{"id"}` | `204` (`409` for the last two) |
| `/account/totp/begin`, `…/confirm` | `{"name"?}`; `{"pending", "code", "name"?}` | `{"secret", "uri", "qr", "pending", "name"}`; `201 {"id", "name"}`, a new app beside any others |
| `/account/totp/rename`, `…/remove` | `{"id", "name"}`; `{"id"}` | `204` (`409` for the last two) |
| `/account/recovery-codes` | `{}` | `{"codes"}`, shown once |
| `/account/password`, `/account/password/remove` | `{"password"}`; `{}` | `204` |
| `/account/sessions/end` | `{"handle"}` | `204` |
| `/logout` | | `204` |

Errors are `{"error", "error_description"}`: `401 authentication_failed` (which
factor was wrong is not said), `401 second_factor_required` and `401
stronger_authentication_required` (the factors cannot reach the `acr` asked
for; nothing is signed in), `401 sign_in_required`, `403 step_up_required`,
`429 rate_limited` with `Retry-After`.  A sign-in's `acr` is the level it
must reach; without one, `mfa`.  Every endpoint that checks a factor is rate limited per client
address and per account, and every attempt is in the audit log, a successful one with the level it
reached.  A client
address (an IPv6 client's /64) may have at most twenty WebAuthn ceremonies
begun and not finished at once (`429`), and the server ten thousand (`503`).

## Signing keys

pyle signs with three keys, each rotated on its own: ES256 for ID tokens,
RS256 for the clients registered with `--rs256`, and an Ed25519 key that is the
root of every biscuit.  Each is created the first time it is needed, and is
stored sealed under a key derived from the root key.

```sh
pyle keys list                  # every key: use, state, kid, created
pyle keys rotate                # all three uses
pyle keys rotate es256 biscuit  # or some of them
```

A key is published from the moment it is announced as `next`, signs once it is
`current`, and stays published as `previous`; `rotate` promotes the waiting
next key and announces a fresh one.  So the first `rotate` only announces:
run it, let clients and services fetch the new key, then run it again.

## OpenID Connect

```sh
pyle client add taxis --redirect https://taxis.example.org/callback \
  --name Taxis --post-logout https://taxis.example.org/ [--scope openid --scope groups] [--rs256] \
  [--min-acr mfa|phr|phrh]
pyle client add taxis-cli --public --redirect http://127.0.0.1/callback
pyle client list
pyle client remove taxis
```

`client add` prints a confidential client's secret once; pyle keeps only its
hash.  Scopes default to `openid profile groups`; `profile` releases the
`name` claim and `groups` the `groups` claim; `offline_access` keeps refresh
tokens alive after the user signs out of pyle; `kleis` lets a client's tokens
obtain kleis attestations.  `--min-acr` is the lowest level a session must
reach to sign in to the client (a short name or an identifier); it defaults
to `mfa`, and `client list` shows it.

| Endpoint | |
| --- | --- |
| `GET /.well-known/openid-configuration` | discovery |
| `GET /jwks` | the ID-token keys: next, current, previous |
| `GET /authorize` (`POST` is redirected to `GET`) | `response_type=code`, `client_id`, `redirect_uri` (exact match), `scope` (with `openid`), `state`, `nonce`, `code_challenge` + `code_challenge_method=S256` (required), `prompt` (`none`, `login`), `max_age`, `acr_values`, `claims` (its `id_token.acr`) |
| `POST /token` | `authorization_code` (`code`, `redirect_uri`, `code_verifier`), `refresh_token` (`refresh_token`, optional narrower `scope`), `urn:ietf:params:oauth:grant-type:device_code` (`device_code`); client authentication `client_secret_basic`, `client_secret_post` or `none` |
| `GET`/`POST /userinfo` | `Authorization: Bearer <access token>`; `sub`, `pyle_account_acr`, and `name` / `groups` as the scope allows |
| `GET`/`POST /end_session` | RP-initiated logout: `id_token_hint`, `client_id`, `post_logout_redirect_uri` (registered with `--post-logout`), `state`; asks before signing out (`POST /end_session/confirm`), then shows a link back to the registered address |

The authorization response carries `code`, `state` and `iss` (RFC 9207).
Codes live 60 seconds and are good once; a code presented a second time
revokes the refresh-token family its first use began, but not the ID token and
access token already issued, which are self-contained and short-lived.  Refresh
tokens rotate on every use; presenting one twice revokes its family.  A family
expires `refreshTokenSeconds` after it began, however often it rotates, and —
unless the grant included `offline_access` — when the pyle session it came
from ends.  ID tokens carry `iss sub aud exp iat auth_time nonce amr acr
pyle_account_acr`, plus `name` with the `profile` scope and `groups` with the
`groups` scope; `sub` is the account's random handle in base64url, `amr` the
RFC 8176 methods (`hwk`/`swk`, `user`, `otp`, `pwd`, `mfa`, and `rec` for a
recovery code), `acr` the session's level, and `pyle_account_acr` the
strongest level the account could sign in at with what it has registered
(absent if it could not sign in again) — so a service can tell an account
that has no passkey from one that chose not to use it.

**Asking for a level.**  The session must reach the client's `--min-acr`
(`mfa` by default), and a request may ask for more:

- `acr_values`: a space-separated list in order of preference.  pyle reads
  the three identifiers, the bare `mfa` (an alias kept from earlier versions)
  and REFEDS MFA 2.0's `https://refeds.org/profile/mfa/phr` (as `phr`), and
  ignores anything else, REFEDS SFA included; any listed level will do, so the session must reach
  the weakest of them.  `acr_values=phr` asks for a passkey.
- `claims`, with `{"id_token": {"acr": {"essential": true, "values": […]}}}`
  (OpenID Connect Core §5.5): read the same way, and since the claim is
  essential the ID token's `acr` is then the first listed value the session
  meets — `https://refeds.org/profile/mfa` for a passkey session asked for
  `["https://refeds.org/profile/mfa"]`, as the REFEDS MFA Profile requires — and
  a request none of whose values pyle knows is refused with
  `unmet_authentication_requirements`.  When `claims` asks about `acr`,
  `acr_values` is not read.

Otherwise the ID token's `acr` is the session's own level, which may be more
than was asked.  `/token` checks the client's minimum again, as it is at the
time: a code or refresh token whose sign-in is below it gets `invalid_grant`,
and a refresh token's whole family is revoked.  Discovery lists the three
identifiers in `acr_values_supported`.

A request that needs a signed-in user sends the browser to
`/signin?return=<path>`, with `max_age=` when it needs a recent sign-in and
`acr=<level>` for the level it needs; the sign-in page offers only the ways in
that reach it.  Under `prompt=none` the client gets `login_required` instead
(no session, or one too old) or `interaction_required` (a level too low).
`max_age=0` is `prompt=login`; when the authentication is too old, the way back
carries `pyle_auth_after=<time>` instead of `prompt` and `max_age`, so it
cannot loop.

## Access tokens

The `access_token` is a biscuit signed by the biscuit root key, whose authority
block is

```
user("alice");
amr("hwk"); amr("user");
acr("phrh");
account_acr("phrh");
auth_time(2026-10-25T10:00:00Z);
group("admin");
client("taxis");
scope("openid"); scope("groups");
check if time($t), $t < 2026-10-25T11:00:00Z;
check if audience($a), {"pyle", "taxis"}.contains($a);
```

A service verifies it offline against the keys of `GET /biscuit/keys`
(`{"keys": [{"kid", "state", "public_key": "ed25519/<hex>"}]}`) with
`Pyle/Token/Verify.lean`, which depends only on `lean-biscuit` and can be copied
as it is:

```lean
match Pyle.Token.verify roots "taxis" now token "allow if group(\"admin\");" with
| .ok identity => -- identity.user, .amr, .acr, .accountAcr, .groups, .client, .authTime
| .error why => -- refuse
```

`acr` is the level of the sign-in and `account_acr` the account's strongest,
as identifiers, when the token was issued.  Holders may attenuate it (append a
block of checks); the identity is read from the authority block only.

## Device grant (RFC 8628)

`POST /device_authorization` (`client_id`, `scope`; confidential clients
authenticate as at `/token`) answers `device_code`, `user_code` (`XXXX-XXXX`),
`verification_uri` (`<issuer>/device`), `verification_uri_complete`,
`expires_in` and `interval`.  The user approves or denies at `/device`, which
needs a session at `phr` or better — signed in with a passkey or a security key
that verifies the user — or at the client's `--min-acr` if that is higher, and
the poll checks the approving session's level against it once more.  The tokens state the approving session's `amr` and
level.  The client polls
`/token` with the device-code grant and gets `authorization_pending`,
`slow_down` (which adds five seconds to the interval), `access_denied`,
`expired_token`, or its tokens once; another client's poll changes nothing.
Its refresh tokens are not tied to the browser session that approved them.

## kleis attestation

`POST /kleis/attest` with `Authorization: Bearer <access token>` — a token
granted the scope `kleis`, which a client must be registered for
(`--scope openid --scope kleis`) — or
`POST /kleis/attest/session` from a signed-in browser, takes a form with
`request`, a kleis biscuit's third-party block request in base64url, and
answers `{"block": <third-party block contents, base64url>, "public_key":
"ed25519/<hex>", "expires": <unix time>}`.  The block states `user`, `amr`,
`acr` and `group` facts and expires after `attestationSeconds` (five minutes).
pyle attests only a sign-in at `kleisMinAcr` or better (`mfa` by default; a
token from before levels counts as `mfa`), and answers `403 insufficient_acr`
otherwise, so a grant that trusts pyle's `user` is never met by a password
alone.  Append
it to the kleis token, and a kleis grant can name the user:

```
check if user($u), ["alice"].contains($u) trusting ed25519/<hex from /biscuit/keys>;
```

The key is the biscuit root key: rotating it (`pyle keys rotate biscuit`)
changes what such grants must trust.

## Forward authentication

For Caddy's `forward_auth` or Traefik's `forwardAuth`:

```json
"trustedProxies": ["127.0.0.1"],
"forwardAuthSecret": "<32 random characters>",
"forwardAuthHosts": {
  "grafana.example.org": "allow if group(\"ops\");",
  "wiki.example.org": "deny if path($p), $p.starts_with(\"/admin\");\nallow if user($u);",
  "vault.example.org": {"policy": "allow if group(\"ops\");", "minAcr": "phr"}
}
```

```
grafana.example.org {
  route {
    request_header -Remote-User
    request_header -Remote-Groups
    forward_auth 127.0.0.1:8420 {
      uri /forward-auth
      header_up X-Pyle-Forward-Auth "<the forwardAuthSecret>"
      copy_headers Remote-User Remote-Groups
    }
    reverse_proxy 127.0.0.1:3000
  }
}
```

`GET /forward-auth` believes `X-Forwarded-Host`, `-Uri`, `-Method` and
`-Proto` only from `trustedProxies`, and answers only requests carrying
`forwardAuthSecret` in `X-Pyle-Forward-Auth`; a configuration with
`forwardAuthHosts` and no secret is refused.  Keep `/forward-auth` off the
public virtual host as well (see [Deployment](#deployment)): pyle answers it,
and `/forward-auth/grant`, only at exactly that path, so a proxy rule on the
path cannot be dodged by spelling it `//forward-auth` or `/forward-auth/`.

Each policy is datalog over `user($u)`, `group($g)`, `host($h)`, `path($p)`,
`method($m)`, and how the session signed in: `acr($a)` (its level, as an
identifier), `amr($m)` (one per RFC 8176 value) and `account_acr($a)` (the
account's strongest level); a host not listed, or no matching `allow`, is
refused.  A host is a policy, or `{"policy", "minAcr"}` with the lowest level a
session must reach (`mfa`, `phr`, `phrh`); a plain policy has the `mfa`
floor.  A session below a host's minimum is sent round the grant to sign in
again at that level (a non-`GET` request gets `401`), before the policy is
asked.  `acr` facts are exact: say "at least" with `minAcr`.  `path` is
the normalised path, without the query: escapes of unreserved characters
decoded, `//` collapsed, `.` and `..` segments removed — so `//admin`,
`/./admin`, `/x/../admin` and `/%61dmin` are all `/admin`.  A path with a
backslash, a control character (escaped or not), `%2F` or `%5C`, or a `..`
left after that is refused with `400`.  Allowed requests get `200` with
`Remote-User` and `Remote-Groups`.

A browser without the host's cookie is sent (`302`) to
`<issuer>/forward-auth/grant?rd=<original URL>&state=…`, and given a
short-lived `__Host-pyle-forward-state` cookie on the protected host.  Once
signed in, the grant returns it through `https://<host>/.pyle/forward-auth?code=…`;
the proxy passes that request to pyle too, and pyle answers it — only for the
browser holding the matching state cookie — by setting the host's own
`__Host-pyle-forward` cookie and going back to the original path, which must
begin with exactly one `/`.  The cookie is tied to the pyle session: signing
out ends it.

## Configuration for the protocols

Optional, with their defaults: `accessTokenSeconds` (3600), `idTokenSeconds`
(600), `refreshTokenSeconds` (thirty days), `deviceCodeSeconds` (600),
`devicePollSeconds` (5), `attestationSeconds` (300), `kleisMinAcr` (`mfa`),
`forwardAuthHosts` (none),
`forwardAuthCookieSeconds` (eight hours) and `forwardAuthSecret` (none; at
least 16 characters, and required when `forwardAuthHosts` is set).



## Deployment

pyle speaks plain HTTP on the loopback and expects a reverse proxy in front
that terminates TLS.  The examples are for **Caddy 2.11.2 or later**: from
2.10.0 until 2.11.2, `forward_auth`'s `copy_headers` let a header the client
sent through when the auth service did not set it
([GHSA-7r4p-vjf4-gxv4](https://github.com/caddyserver/caddy/security/advisories/GHSA-7r4p-vjf4-gxv4)).
pyle sends no `Remote-Groups` for a user in no group, so on an affected Caddy
such a user could send `Remote-Groups: admin` and have it believed.  The
examples strip both headers before `forward_auth` themselves, which makes
them safe on older releases too.

For pyle at `auth.example.org` and a service it protects at
`wiki.example.org`, with this `pyle.json`:

```json
{
  "issuer": "https://auth.example.org",
  "rpId": "auth.example.org",
  "origins": ["https://auth.example.org"],
  "database": "/var/lib/pyle/pyle.db",
  "rootKeyFile": "/var/lib/pyle/root.key",
  "trustedProxies": ["127.0.0.1"],
  "forwardAuthSecret": "<32 random characters>",
  "forwardAuthHosts": {
    "wiki.example.org": "allow if group(\"staff\");"
  }
}
```

```
auth.example.org {
  # The check is for the proxy alone, in every spelling of its path.
  # /forward-auth/grant, where the browser goes to sign in, stays public.
  @fa path_regexp ^/+forward-auth/*$
  respond @fa 404
  reverse_proxy 127.0.0.1:8420
}

wiki.example.org {
  route {
    # Whatever the client sent under these names never reaches the service.
    request_header -Remote-User
    request_header -Remote-Groups
    # Every request is asked about, /.pyle/forward-auth?code=… included: pyle
    # answers that one itself, with a 302 that sets the host's cookie, and
    # Caddy hands the 302 to the browser.
    forward_auth 127.0.0.1:8420 {
      uri /forward-auth
      header_up X-Pyle-Forward-Auth "<the forwardAuthSecret>"
      copy_headers Remote-User Remote-Groups
    }
    reverse_proxy 127.0.0.1:3000
  }
}
```

**Keep it in a `route`.**  Outside one, Caddy orders directives itself, not
as written: `rewrite`, `uri` and `try_files` always run before
`forward_auth`, so pyle would judge the rewritten path, and a rewrite could
turn `/.pyle/forward-auth` into something else; `handle_path` strips its
prefix after it, so the service sees a different path from the one pyle
judged.  Inside a `route` directives run in the order written: put the strips
and `forward_auth` first, and any rewriting of the service's after them.

**`trustedProxies`** names Caddy's address as pyle sees it, as exact
addresses: no CIDR ranges.  pyle believes `X-Forwarded-For` and the
`X-Forwarded-Host`, `-Uri`, `-Method` and `-Proto` of forward
authentication only from those addresses.  If it is wrong, forward
authentication refuses everything, and every client shares Caddy's address
as its rate-limit key, so one person's failed sign-ins slow down everyone's.

**Services with an API of their own.**  A service whose API scripts call with
its own bearer tokens can let those requests past pyle, on the API's paths
and with a `Bearer` credential only:

```
api.example.org {
  @api {
    path /api/v1/*
    header Authorization "Bearer *"
  }
  handle @api {
    request_header -Remote-User
    request_header -Remote-Groups
    reverse_proxy 127.0.0.1:8090
  }
  handle {
    route { … as for wiki.example.org … }
  }
}
```

Anyone can send `Authorization: Bearer x`.  On the bypassed paths the
service's own authentication is then the only barrier, so list only paths
that refuse every request without a valid token of the service's, never a
login endpoint or anything open for reading, and never bypass in front of a
service that trusts `Remote-User`.

### First run

```sh
pyle init                          # the root key (mode 0600) and the database
pyle keys rotate                   # announce the first ES256, RS256 and biscuit keys…
pyle keys rotate                   # …and make them current
pyle invite alice --group admin    # open the link it prints, on a device with a passkey
pyle client add wiki --name Wiki --redirect https://wiki.example.org/oauth/callback \
  --post-logout https://wiki.example.org/
```

The keys are made on first use if this is skipped; rotating twice up front
only means the first clients find a `next` key in `/jwks` already.  `client
add` prints the secret once.  Then have alice add a second passkey or a
security key from `/account`, so that losing a phone does not lock her out.

### Upgrading

pyle migrates its database when it opens it, and refuses one written by a
newer pyle.  Migration 6 makes room for several authenticator apps per
account: an account's one TOTP secret becomes its app named "Authenticator
app", which goes on working with the same codes, and its failed-code count
and lock carry over to the account.  Its last use is shown when the step it
last accepted came more than a minute after it was set up, and as not used
otherwise.  There is no way back to an older pyle after it, short of a backup.

### Docker

`docker/Dockerfile` builds an image with `pyle` alone, published as
`ghcr.io/chrisflav/pyle` (`latest` from master, and each commit's full sha).
It runs as uid 991, reads `PYLE_CONFIG=/pyle/config/pyle.json`, and keeps its
state in the volume `/pyle/data`; the health check asks `/healthz` on port
8420.  The configuration must say `"host": "0.0.0.0"` and name the state by
absolute path (`/pyle/data/pyle.db`, `/pyle/data/root.key`):

```sh
docker volume create pyle-data
docker run --rm -v pyle-data:/pyle/data -v "$PWD/config:/pyle/config:ro" \
  ghcr.io/chrisflav/pyle init
docker run -d --name pyle -p 127.0.0.1:8420:8420 \
  -v pyle-data:/pyle/data -v "$PWD/config:/pyle/config:ro" ghcr.io/chrisflav/pyle
docker exec pyle pyle invite alice --group admin
```

With Caddy on the host and the port published like this, pyle sees Caddy's
connections coming from the bridge's gateway, not from `127.0.0.1`: put that
address in `trustedProxies` (`docker network inspect bridge`, usually
`172.17.0.1`).  With Caddy in a container too, give both a user-defined
network with fixed addresses and name Caddy's.

### Backups

Two files are the whole state: the database and the root key.  The database
holds the accounts, credentials, sessions, clients and the audit log; the
root key encrypts the signing keys and the TOTP secrets inside it, so a
database without its root key is useless.  Copy the root key once, offline,
when it is made: it never changes.  Back the database up with SQLite rather
than by copying the file under a running server, and keep the copy private:

```sh
umask 077
sqlite3 /var/lib/pyle/pyle.db ".backup '/backup/pyle-$(date +%F).db'"
```

The image has no `sqlite3`.  Stop the container, copy, and start it again:

```sh
docker stop pyle
docker run --rm -v pyle-data:/pyle/data:ro -v /backup:/backup debian:bookworm-slim \
  sh -c 'umask 077 && cp /pyle/data/pyle.db "/backup/pyle-$(date +%F).db"'
docker start pyle
```

To restore, put both back, check them with `pyle audit verify`, and start
the server.  A restored database brings back sessions and refresh tokens as
they were.

**If a backup leaks.**  The database alone gives away hashes (of sessions,
refresh tokens, client secrets, recovery codes and passwords) and secrets
sealed under the root key, none of them usable as they are.  The database
*with* the root key gives away more: whoever has both can make
forward-authentication cookies for every session still alive and read every
TOTP secret, and can sign tokens with the keys they held.  `pyle keys rotate`
replaces the signing keys, twice to retire the old ones, but nothing in pyle
yet replaces the root key or ends every session at once (DESIGN.md §12): the
remedy today is a fresh `pyle init` and new invitations.

### Verifying access tokens in a service

A service in Lean copies `Pyle/Token/Verify.lean`, which needs only
`lean-biscuit`, fetches the root keys from `GET /biscuit/keys` (every one
listed, `next` and `previous` too) and refreshes them now and then, for
instance when a token fails under all of them:

```lean
open LeanBiscuit in
def roots (keys : List String) : List PublicKey :=  -- each "ed25519/<hex>"
  keys.filterMap fun k => do
    let hex ← k.dropPrefix? "ed25519/"
    return { algorithm := .ed25519, key := ← Bytes.ofHex? hex.toString }

match Pyle.Token.verify (roots published) "wiki" now bearer "allow if group(\"staff\");" with
| .ok who => -- who.user, who.groups, who.amr, who.client, who.authTime, who.scopes
| .error why => -- 401
```

The service name is the client id the token was issued to: the token checks
that it is used there or at pyle and nowhere else.  A service in another
language verifies it with any biscuit library, giving the facts
`time(<now>)` and `audience("<client id>")` and reading `user`, `group` and
`amr` from the authority block only.  One that would rather not verify
anything asks `GET /userinfo` with the token.

### diff-reviewer, taxis and orchestra

None of the three reads `Remote-User` or speaks OpenID Connect yet, so pyle
in front of them is a second gate, not single sign-on: their own sign-in
stays, and a pyle session alone does not sign anyone in to them.

- **diff-reviewer.**  Put the host behind `forward_auth`, with a policy such
  as `allow if group("admin");`, and bypass `/api/v1/*` and `/api/agent/v1/*`
  with `Bearer` as above: the API token (scripts, orchestra) and the agent
  token (injected by kleis) keep working, and on those paths they are the
  only barrier.  The password login, `POST /api/login`, is then behind pyle
  for anyone coming through Caddy, but still answers on diff-reviewer's own
  port (`127.0.0.1:8090` by default) to anything on that machine.  Add
  Caddy's address to `--trusted-proxy` as before.
- **taxis.**  Run it in private mode (`auth.private`): open mode answers reads
  with no credential, which would make any bypass a way to read everything.
  Bypass `/api/*` and `/mcp` with `Bearer` for bots, but not `/api/auth/*`,
  where the password and OAuth sign-ins are (add `not path /api/auth/*` to
  the matcher); on the bypassed paths, taxis's API tokens are the only
  barrier.  For sign-in through pyle, taxis needs an OpenID Connect provider
  of its own; the client for it would be `pyle client add taxis --name Taxis
  --redirect https://taxis.example.org/auth/pyle/callback --post-logout
  https://taxis.example.org/`, with the `groups` claim feeding
  `auth.readGroups`.
- **orchestra.**  The dashboard (`orchestrad dashboard`) takes its password
  as a cookie or as `Authorization: Bearer`, which the `orchestra` CLI and
  orchestra-app send.  Bypass `/api/v1/*` and `/sse/v1/*` with `Bearer` for
  them; there the bearer *is* the password, so every request on those paths
  is a guess at it that pyle never sees, and the password's length is the
  only barrier.  `POST /api/login` stays behind pyle.  A browser's SSE stream
  that reconnects after the forward-auth cookie has expired
  (`forwardAuthCookieSeconds`, eight hours) gets a redirect instead of
  events, and the page must be reloaded.