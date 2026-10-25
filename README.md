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
`sessionIdleSeconds` (eight hours), `sessionAbsoluteSeconds` (thirty days) and
`trustedProxies` (peer addresses whose `X-Forwarded-For` is believed; none by
default).  Relative paths are relative to the configuration file.  Unknown keys
are an error.

```sh
pyle init --config pyle.json        # create the root key (mode 0600) and the database
pyle serve --config pyle.json       # answer HTTP; put a TLS-terminating proxy in front
pyle user add alice --group admin   # create an account
pyle user list                      # list the accounts
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

The server answers `GET /healthz` and `POST /logout` (end the browser's
session), and the protocols below.

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
hash.  Scopes default to `openid profile groups`; `kleis` lets a client's
tokens obtain kleis attestations.

| Endpoint | |
| --- | --- |
| `GET /.well-known/openid-configuration` | discovery |
| `GET /jwks` | the ID-token keys: next, current, previous |
| `GET /authorize` (`POST` is redirected to `GET`) | `response_type=code`, `client_id`, `redirect_uri` (exact match), `scope` (with `openid`), `state`, `nonce`, `code_challenge` + `code_challenge_method=S256` (required), `prompt` (`none`, `login`), `max_age`, `acr_values` (`phr`) |
| `POST /token` | `authorization_code` (`code`, `redirect_uri`, `code_verifier`), `refresh_token` (`refresh_token`, optional narrower `scope`), `urn:ietf:params:oauth:grant-type:device_code` (`device_code`); client authentication `client_secret_basic`, `client_secret_post` or `none` |
| `GET`/`POST /userinfo` | `Authorization: Bearer <access token>`; `sub`, `name`, `groups` |
| `GET /logout` | RP-initiated logout: `id_token_hint`, `client_id`, `post_logout_redirect_uri` (registered with `--post-logout`), `state`; asks before signing out (`POST /logout/confirm`) |

The authorization response carries `code`, `state` and `iss` (RFC 9207).
Codes live 60 seconds and are good once.  Refresh tokens rotate on every use;
presenting one twice revokes its family.  ID tokens carry `iss sub aud exp iat
auth_time nonce amr acr name groups`, where `sub` is the account's random
handle in base64url and `acr` is `phr` for a passkey or security key with user
verification, `mfa` otherwise.

A request that needs a signed-in user sends the browser to
`/signin?return=<path>` (with `max_age=` and `acr=phr` when it needs a recent
or phishing-resistant sign-in).

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
`slow_down`, `access_denied`, `expired_token`, or its tokens once.

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
`-Proto` only from `trustedProxies`.  Each policy is datalog over `user($u)`,
`group($g)`, `host($h)`, `path($p)` and `method($m)`; a host not listed, or
no matching `allow`, is refused.  Allowed requests get `200` with
`Remote-User` and `Remote-Groups`.  A browser without the host's cookie is
sent (`302`) to `<issuer>/forward-auth/grant?rd=<original URL>`, which, once
signed in, returns it through `https://<host>/.pyle/forward-auth?code=…`; the
proxy passes that request to pyle too, and pyle answers it by setting the
host's own `__Host-pyle-forward` cookie.  The cookie is tied to the pyle
session: signing out ends it.

## Configuration for the protocols

Optional, with their defaults: `accessTokenSeconds` (3600), `idTokenSeconds`
(600), `refreshTokenSeconds` (thirty days), `deviceCodeSeconds` (600),
`devicePollSeconds` (5), `attestationSeconds` (300), `forwardAuthHosts` (none)
and `forwardAuthCookieSeconds` (eight hours).