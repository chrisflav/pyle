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
first passkey and is signed in with it.  From `/account` they can then add
more passkeys and security keys, an authenticator app (TOTP), recovery codes,
and — if `allowPasswords` is set — a password, and see and end their sessions.
The account page nags until two authenticators are registered, and the last
two cannot be removed.

A session needs a passkey (WebAuthn with user verification) or two distinct
factors: a security key without user verification, a TOTP code, a recovery
code, a password.  A password or a code alone never signs anyone in.  Adding
or removing a way in needs a fresh authentication within the last five
minutes.

Pages, served with no third-party code under a strict CSP:

| | |
| --- | --- |
| `GET /signin?return=<path>[&max_age=<s>][&acr=phr]` | sign in, or step up the current session; then `303` to `return`, which must be a path on this origin |
| `GET /account` | the account |
| `GET /invite/<token>` | register an invited account's first passkey |
| `GET /assets/pyle.js`, `GET /assets/pyle.css` | the pages' script and stylesheet |

The JSON endpoints behind them (`POST`, `Origin` checked, binary values in
base64url):

| | body | answer |
| --- | --- | --- |
| `/signin/webauthn/begin` | `{}` (passkey) or `{"name"}` (security key) | WebAuthn request options |
| `/signin/webauthn/finish` | `{"credential", "totp"?, "recovery"?, "password"?, "return"?}` | `{"redirect", "amr", "acr"}` and the session cookie |
| `/signin/stepup/begin`, `/signin/stepup/finish` | as above, for the current session | as above |
| `/signin/codes` | `{"name"}` and two of `"password"`, `"totp"`, `"recovery"`; `"return"`? | as above |
| `/invite/<token>/begin`, `/invite/<token>/finish` | `{}`; `{"credential", "name"?}` | creation options; `201 {"name"}` |
| `/account/authenticators/register/begin`, `…/finish` | `{}`; `{"credential", "name"?}` | creation options; `201 {"id"}` |
| `/account/authenticators/rename`, `…/remove` | `{"id", "name"}`; `{"id"}` | `204` (`409` for the last two) |
| `/account/totp/begin`, `…/confirm`, `…/remove` | `{}`; `{"pending", "code"}`; `{}` | `{"secret", "uri", "pending"}`; `204`; `204` |
| `/account/recovery-codes` | `{}` | `{"codes"}`, shown once |
| `/account/password`, `/account/password/remove` | `{"password"}`; `{}` | `204` |
| `/account/sessions/end` | `{"handle"}` | `204` |
| `/logout` | | `204` |

Errors are `{"error", "error_description"}`: `401 authentication_failed` (which
factor was wrong is not said), `401 second_factor_required`, `401
sign_in_required`, `403 step_up_required`, `429 rate_limited` with
`Retry-After`.  Every endpoint that checks a factor is rate limited per client
address and per account, and every attempt is in the audit log.  A client
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
  --name Taxis --post-logout https://taxis.example.org/ [--scope openid --scope groups] [--rs256]
pyle client add taxis-cli --public --redirect http://127.0.0.1/callback
pyle client list
pyle client remove taxis
```

`client add` prints a confidential client's secret once; pyle keeps only its
hash.  Scopes default to `openid profile groups`; `profile` releases the
`name` claim and `groups` the `groups` claim; `offline_access` keeps refresh
tokens alive after the user signs out of pyle; `kleis` lets a client's tokens
obtain kleis attestations.

| Endpoint | |
| --- | --- |
| `GET /.well-known/openid-configuration` | discovery |
| `GET /jwks` | the ID-token keys: next, current, previous |
| `GET /authorize` (`POST` is redirected to `GET`) | `response_type=code`, `client_id`, `redirect_uri` (exact match), `scope` (with `openid`), `state`, `nonce`, `code_challenge` + `code_challenge_method=S256` (required), `prompt` (`none`, `login`), `max_age`, `acr_values` (`phr`) |
| `POST /token` | `authorization_code` (`code`, `redirect_uri`, `code_verifier`), `refresh_token` (`refresh_token`, optional narrower `scope`), `urn:ietf:params:oauth:grant-type:device_code` (`device_code`); client authentication `client_secret_basic`, `client_secret_post` or `none` |
| `GET`/`POST /userinfo` | `Authorization: Bearer <access token>`; `sub`, and `name` / `groups` as the scope allows |
| `GET`/`POST /end_session` | RP-initiated logout: `id_token_hint`, `client_id`, `post_logout_redirect_uri` (registered with `--post-logout`), `state`; asks before signing out (`POST /end_session/confirm`), then shows a link back to the registered address |

The authorization response carries `code`, `state` and `iss` (RFC 9207).
Codes live 60 seconds and are good once; a code presented a second time
revokes the refresh-token family its first use began, but not the ID token and
access token already issued, which are self-contained and short-lived.  Refresh
tokens rotate on every use; presenting one twice revokes its family.  A family
expires `refreshTokenSeconds` after it began, however often it rotates, and —
unless the grant included `offline_access` — when the pyle session it came
from ends.  ID tokens carry `iss sub aud exp iat auth_time nonce amr acr`, plus
`name` with the `profile` scope and `groups` with the `groups` scope; `sub` is
the account's random handle in base64url and `acr` is `phr` for a passkey or
security key with user verification, `mfa` otherwise.

A request that needs a signed-in user sends the browser to
`/signin?return=<path>` (with `max_age=` and `acr=phr` when it needs a recent
or phishing-resistant sign-in).  `max_age=0` is `prompt=login`; when the
authentication is too old, the way back carries `pyle_auth_after=<time>`
instead of `prompt` and `max_age`, so it cannot loop.

## Access tokens

The `access_token` is a biscuit signed by the biscuit root key, whose authority
block is

```
user("alice");
amr("hwk"); amr("user");
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
| .ok identity => -- identity.user, .amr, .groups, .client, .authTime
| .error why => -- refuse
```

Holders may attenuate it (append a block of checks); the identity is read from
the authority block only.

## Device grant (RFC 8628)

`POST /device_authorization` (`client_id`, `scope`; confidential clients
authenticate as at `/token`) answers `device_code`, `user_code` (`XXXX-XXXX`),
`verification_uri` (`<issuer>/device`), `verification_uri_complete`,
`expires_in` and `interval`.  The user approves or denies at `/device`, which
needs a session signed in with a passkey or security key.  The client polls
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
"ed25519/<hex>", "expires": <unix time>}`.  The block states `user`, `amr` and
`group` facts and expires after `attestationSeconds` (five minutes).  Append
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
"forwardAuthHosts": {
  "grafana.example.org": "allow if group(\"ops\");",
  "wiki.example.org": "deny if path($p), $p.starts_with(\"/admin\");\nallow if user($u);"
}
```

```
grafana.example.org {
  forward_auth 127.0.0.1:8420 {
    uri /forward-auth
    copy_headers Remote-User Remote-Groups
  }
  reverse_proxy 127.0.0.1:3000
}
```

`GET /forward-auth` believes `X-Forwarded-Host`, `-Uri`, `-Method` and
`-Proto` only from `trustedProxies`.  **`/forward-auth` must not be reachable
through the public virtual host**, or `forwardAuthSecret` must be set: then
pyle answers only requests carrying it in `X-Pyle-Forward-Auth` (with Caddy,
`header_up X-Pyle-Forward-Auth <secret>` inside `forward_auth`).

Each policy is datalog over `user($u)`, `group($g)`, `host($h)`, `path($p)` and
`method($m)`; a host not listed, or no matching `allow`, is refused.  `path` is
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
`devicePollSeconds` (5), `attestationSeconds` (300), `forwardAuthHosts` (none),
`forwardAuthCookieSeconds` (eight hours) and `forwardAuthSecret` (none; at
least 16 characters).