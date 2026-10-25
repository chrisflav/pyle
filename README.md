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
without it.  The server so far answers `GET /healthz` and `POST /logout`;
sign-in and OpenID Connect follow (DESIGN.md §11).