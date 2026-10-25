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