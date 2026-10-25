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
and a listed AAGUID can be registered).  Relative paths are relative to the
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
address (and per account where one is named), and every attempt is in the
audit log.

OpenID Connect follows (DESIGN.md §11).