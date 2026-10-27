#!/usr/bin/env python3
"""The browser, the authenticator and the relying parties of the integration test.

`scripts/integration.sh` sets up a pyle and starts it; this drives it over real
HTTP, as a browser with a passkey, as an OpenID Connect client, as a device and
as a reverse proxy would.  It uses the standard library only, so the
cryptography a browser and an authenticator bring along is written out here: an
Ed25519 signer (RFC 8032, section 6) for the passkey and an ES256 verifier for
the ID tokens.  Neither is constant-time, and neither needs to be: the keys are
made for this run and thrown away with it.

Every check prints an `ok` or `FAIL` line, as the shell script's do, and the
tally is written to the file named by `--counts` for the script to add up.
"""

import argparse
import base64
import hashlib
import http.client
import json
import os
import sys
import time
import urllib.parse

PASS = 0
FAIL = 0


def ok(name):
    global PASS
    PASS += 1
    print(f"  ok   {name}", flush=True)


def bad(name, detail=""):
    global FAIL
    FAIL += 1
    print(f"  FAIL {name}", flush=True)
    if detail:
        print(f"       {detail}", flush=True)


def check(cond, name, detail=""):
    if cond:
        ok(name)
    else:
        bad(name, detail)
    return cond


def section(name):
    print(f"\n== {name}", flush=True)


def b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def unb64u(s):
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


# ---------------------------------------------------------------- Ed25519

ED_P = 2**255 - 19
ED_L = 2**252 + 27742317777372353535851937790883648493
ED_D = -121665 * pow(121666, -1, ED_P) % ED_P


def _ed_add(p, q):
    x1, y1, z1, t1 = p
    x2, y2, z2, t2 = q
    a = (y1 - x1) * (y2 - x2) % ED_P
    b = (y1 + x1) * (y2 + x2) % ED_P
    c = 2 * t1 * t2 * ED_D % ED_P
    d = 2 * z1 * z2 % ED_P
    e, f, g, h = b - a, d - c, d + c, b + a
    return (e * f % ED_P, g * h % ED_P, f * g % ED_P, e * h % ED_P)


def _ed_mul(s, p):
    q = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            q = _ed_add(q, p)
        p = _ed_add(p, p)
        s >>= 1
    return q


def _ed_compress(p):
    zinv = pow(p[2], ED_P - 2, ED_P)
    x, y = p[0] * zinv % ED_P, p[1] * zinv % ED_P
    return int.to_bytes(y | ((x & 1) << 255), 32, "little")


_ED_GY = 4 * pow(5, ED_P - 2, ED_P) % ED_P


def _ed_recover_x(y, sign):
    x2 = (y * y - 1) * pow(ED_D * y * y + 1, ED_P - 2, ED_P) % ED_P
    x = pow(x2, (ED_P + 3) // 8, ED_P)
    if (x * x - x2) % ED_P != 0:
        x = x * pow(2, (ED_P - 1) // 4, ED_P) % ED_P
    if (x & 1) != sign:
        x = ED_P - x
    return x


_ED_GX = _ed_recover_x(_ED_GY, 0)
ED_G = (_ED_GX, _ED_GY, 1, _ED_GX * _ED_GY % ED_P)


def _sha512_int(m):
    return int.from_bytes(hashlib.sha512(m).digest(), "little")


def _ed_expand(secret):
    h = hashlib.sha512(secret).digest()
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a, h[32:]


def ed25519_public(secret):
    a, _ = _ed_expand(secret)
    return _ed_compress(_ed_mul(a, ED_G))


def ed25519_sign(secret, msg):
    a, prefix = _ed_expand(secret)
    pub = _ed_compress(_ed_mul(a, ED_G))
    r = _sha512_int(prefix + msg) % ED_L
    rs = _ed_compress(_ed_mul(r, ED_G))
    h = _sha512_int(rs + pub + msg) % ED_L
    s = (r + h * a) % ED_L
    return rs + int.to_bytes(s, 32, "little")


# ---------------------------------------------------------------- P-256

P256_P = 2**256 - 2**224 + 2**192 + 2**96 - 1
P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
P256_A = P256_P - 3
P256_G = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
          0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)


def _p_add(p, q):
    if p is None:
        return q
    if q is None:
        return p
    if p[0] == q[0] and (p[1] + q[1]) % P256_P == 0:
        return None
    if p == q:
        lam = (3 * p[0] * p[0] + P256_A) * pow(2 * p[1], -1, P256_P)
    else:
        lam = (q[1] - p[1]) * pow(q[0] - p[0], -1, P256_P)
    lam %= P256_P
    x = (lam * lam - p[0] - q[0]) % P256_P
    return (x, (lam * (p[0] - x) - p[1]) % P256_P)


def _p_mul(k, p):
    r = None
    while k:
        if k & 1:
            r = _p_add(r, p)
        p = _p_add(p, p)
        k >>= 1
    return r


def es256_verify(x, y, msg, sig):
    """Whether `sig`, in JOSE's r || s form, is an ES256 signature of `msg`
    under the public key (x, y)."""
    if len(sig) != 64:
        return False
    r, s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
    if not (0 < r < P256_N and 0 < s < P256_N):
        return False
    e = int.from_bytes(hashlib.sha256(msg).digest(), "big")
    w = pow(s, -1, P256_N)
    pt = _p_add(_p_mul(e * w % P256_N, P256_G), _p_mul(r * w % P256_N, (x, y)))
    return pt is not None and pt[0] % P256_N == r


# ---------------------------------------------------------------- CBOR

def _cbor_head(major, n):
    if n < 24:
        return bytes([major << 5 | n])
    for ai, size in ((24, 1), (25, 2), (26, 4), (27, 8)):
        if n < 1 << (8 * size):
            return bytes([major << 5 | ai]) + n.to_bytes(size, "big")
    raise ValueError("too large")


def cbor(v):
    """The deterministic encoding of the few CBOR values WebAuthn needs."""
    if isinstance(v, bool):
        return b"\xf5" if v else b"\xf4"
    if isinstance(v, int):
        return _cbor_head(0, v) if v >= 0 else _cbor_head(1, -1 - v)
    if isinstance(v, bytes):
        return _cbor_head(2, len(v)) + v
    if isinstance(v, str):
        b = v.encode()
        return _cbor_head(3, len(b)) + b
    if isinstance(v, list):
        return _cbor_head(4, len(v)) + b"".join(cbor(x) for x in v)
    if isinstance(v, dict):
        items = sorted((cbor(k), cbor(x)) for k, x in v.items())
        return _cbor_head(5, len(items)) + b"".join(k + x for k, x in items)
    raise TypeError(type(v))


# ---------------------------------------------------------------- a passkey

class Passkey:
    """A software authenticator holding one Ed25519 credential, with user
    verification: what a phone or a security key with a PIN would be."""

    def __init__(self, rp_id, origin):
        self.rp_id, self.origin = rp_id, origin
        self.secret = os.urandom(32)
        self.id = os.urandom(16)
        self.handle = b""
        self.counter = 0

    def _client_data(self, typ, challenge, origin):
        return json.dumps({"type": typ, "challenge": challenge, "origin": origin,
                           "crossOrigin": False}, separators=(",", ":")).encode()

    def create(self, options):
        """What `navigator.credentials.create` returns: attestation `none`."""
        self.handle = unb64u(options["user"]["id"])
        cose = {1: 1, 3: -8, -1: 6, -2: ed25519_public(self.secret)}
        auth_data = (hashlib.sha256(self.rp_id.encode()).digest() + bytes([0x45])
                     + (0).to_bytes(4, "big") + bytes(16)
                     + len(self.id).to_bytes(2, "big") + self.id + cbor(cose))
        cd = self._client_data("webauthn.create", options["challenge"], self.origin)
        ao = cbor({"fmt": "none", "attStmt": {}, "authData": auth_data})
        return {"id": b64u(self.id), "clientDataJSON": b64u(cd),
                "attestationObject": b64u(ao), "transports": ["internal"]}

    def assert_(self, options, origin=None):
        """What `navigator.credentials.get` returns."""
        self.counter += 1
        auth_data = (hashlib.sha256(self.rp_id.encode()).digest() + bytes([0x05])
                     + self.counter.to_bytes(4, "big"))
        cd = self._client_data("webauthn.get", options["challenge"], origin or self.origin)
        sig = ed25519_sign(self.secret, auth_data + hashlib.sha256(cd).digest())
        return {"id": b64u(self.id), "clientDataJSON": b64u(cd),
                "authenticatorData": b64u(auth_data), "signature": b64u(sig),
                "userHandle": b64u(self.handle)}


# ---------------------------------------------------------------- HTTP

class Reply:
    def __init__(self, status, headers, body):
        self.status, self.headers, self.body = status, headers, body

    def header(self, name):
        for k, v in self.headers:
            if k.lower() == name.lower():
                return v
        return None

    def all(self, name):
        return [v for k, v in self.headers if k.lower() == name.lower()]

    @property
    def location(self):
        return self.header("Location") or ""

    @property
    def text(self):
        return self.body.decode(errors="replace")

    def json(self):
        try:
            return json.loads(self.body)
        except ValueError:
            return {}

    def cookie(self, name):
        """The value a reply sets for a cookie, or None."""
        for v in self.all("Set-Cookie"):
            k, _, rest = v.partition("=")
            if k == name:
                return rest.split(";")[0]
        return None

    def __repr__(self):
        return f"{self.status} {self.text[:300]!r}"


class Client:
    """One HTTP peer: a connection to pyle, with no redirects followed and the
    cookies kept by hand.  pyle's cookies are `__Host-` and `Secure`, which a
    real browser would refuse over plain HTTP; the test keeps them anyway, since
    what is under test is what pyle sets and reads, not the browser's rules."""

    def __init__(self, host, port, origin, address):
        self.host, self.port, self.origin = host, port, origin
        self.address = address
        self.cookies = {}

    def request(self, method, path, body=None, headers=None, form=None, js=None,
                cookies=True):
        # The test connects from 127.0.0.1, a trusted proxy, so that each
        # party can be given an address of its own: as behind Caddy, the rate
        # limiter then counts each one's failures separately.
        h = {"X-Forwarded-For": self.address}
        h.update(headers or {})
        if js is not None:
            body = json.dumps(js).encode()
            h.setdefault("Content-Type", "application/json")
        if form is not None:
            body = urllib.parse.urlencode(form).encode()
            h.setdefault("Content-Type", "application/x-www-form-urlencoded")
        if cookies and self.cookies:
            h["Cookie"] = "; ".join(f"{k}={v}" for k, v in self.cookies.items())
        conn = http.client.HTTPConnection(self.host, self.port, timeout=30)
        try:
            conn.request(method, path, body=body, headers=h)
            r = conn.getresponse()
            reply = Reply(r.status, r.getheaders(), r.read())
        finally:
            conn.close()
        if cookies:
            for v in reply.all("Set-Cookie"):
                k, _, rest = v.partition("=")
                val = rest.split(";")[0]
                if val and "Max-Age=0" not in v:
                    self.cookies[k] = val
                else:
                    self.cookies.pop(k, None)
        return reply

    def get(self, path, **kw):
        return self.request("GET", path, **kw)

    def post_json(self, path, js, **kw):
        h = {"Origin": self.origin}
        h.update(kw.pop("headers", {}))
        return self.request("POST", path, js=js, headers=h, **kw)

    def post_form(self, path, form, origin=True, **kw):
        h = {"Origin": self.origin} if origin else {}
        h.update(kw.pop("headers", {}))
        return self.request("POST", path, form=form, headers=h, **kw)


def path_of(url):
    """The path and query of an absolute URL."""
    u = urllib.parse.urlsplit(url)
    return u.path + ("?" + u.query if u.query else "")


def query_of(url):
    return dict(urllib.parse.parse_qsl(urllib.parse.urlsplit(url).query))


def basic(client_id, secret):
    raw = f"{urllib.parse.quote(client_id)}:{urllib.parse.quote(secret)}".encode()
    return {"Authorization": "Basic " + base64.b64encode(raw).decode()}


def jwt_parts(token):
    h, p, s = token.split(".")
    return json.loads(unb64u(h)), json.loads(unb64u(p)), (h + "." + p).encode(), unb64u(s)


# ---------------------------------------------------------------- the run

def run(a):
    origin = a.issuer
    rp_id = urllib.parse.urlsplit(a.issuer).hostname
    browser = Client("127.0.0.1", a.port, origin, "198.51.100.1")
    rp = Client("127.0.0.1", a.port, origin, "203.0.113.1")
    # The refusals are provoked from an address of their own: the rate limiter
    # rightly holds an address's failures against it, and the user's own
    # browser should not be slowed down by the test's attacks.
    mallory = Client("127.0.0.1", a.port, origin, "192.0.2.13")
    key = Passkey(rp_id, origin)
    invite = path_of(a.invite)

    # ------------------------------------------------------------ invitation
    section("invitation and the first passkey")
    r = browser.get(invite)
    check(r.status == 200 and "<html" in r.text.lower(), "the invitation page is served", repr(r))
    r = browser.post_json(invite + "/begin", {})
    opts = r.json()
    check(r.status == 200 and "challenge" in opts, "the invitation offers creation options",
          repr(r))
    check(opts.get("rp", {}).get("id") == rp_id, "for this relying party", repr(opts.get("rp")))
    check(opts.get("authenticatorSelection", {}).get("userVerification") == "required",
          "requiring user verification", repr(opts.get("authenticatorSelection")))
    algs = [p.get("alg") for p in opts.get("pubKeyCredParams", [])]
    check(-8 in algs, "and offering EdDSA", repr(algs))
    cred = key.create(opts)
    r = browser.post_json(invite + "/begin", {}, headers={"Origin": "http://evil.example"})
    check(r.status == 403, "a cross-origin begin is refused", repr(r))
    r = browser.post_json(invite + "/finish", {"credential": cred, "name": "e2e passkey"})
    check(r.status == 201 and r.json().get("name") == a.user,
          "the passkey is registered and the account created", repr(r))
    r = mallory.post_json(invite + "/finish", {"credential": cred})
    check(r.status >= 400, "a registration response is good once", repr(r))
    r = mallory.post_json(invite + "/begin", {})
    check(r.status >= 400, "the invitation is spent", repr(r))

    # ------------------------------------------------------------ sign-in
    section("sign-in with the passkey")
    r = browser.get("/account")
    check(r.status in (302, 303) and r.location.startswith("/signin"),
          "without a session the account page sends to sign in", repr(r))
    r = browser.get("/signin?return=/account")
    check(r.status == 200, "the sign-in page is served", repr(r))
    csp = r.header("Content-Security-Policy") or ""
    check("frame-ancestors 'none'" in csp, "under a strict CSP", csp)
    check(r.header("X-Content-Type-Options") == "nosniff", "with nosniff")
    r = mallory.post_json("/signin/webauthn/begin", {})
    check(r.status == 200, "a sign-in ceremony begins", repr(r))
    wrong = key.assert_(r.json(), origin="http://evil.example")
    r = mallory.post_json("/signin/webauthn/finish", {"credential": wrong, "return": "/account"})
    check(r.status == 401 and not r.cookie("__Host-pyle"),
          "an assertion made for another origin signs nobody in", repr(r))
    r = browser.post_json("/signin/webauthn/begin", {})
    asserted = key.assert_(r.json())
    r = browser.post_json("/signin/webauthn/finish",
                          {"credential": asserted, "return": "/account"})
    body = r.json()
    check(r.status == 200 and body.get("redirect") == "/account", "the passkey signs in",
          repr(r))
    check(body.get("acr") == "phrh" and "user" in body.get("amr", []),
          "phishing-resistantly, with user verification, from a device-bound key", repr(body))
    session = r.cookie("__Host-pyle")
    check(bool(session), "and sets the session cookie")
    setc = " ".join(r.all("Set-Cookie"))
    check("HttpOnly" in setc and "Secure" in setc and "SameSite=Lax" in setc,
          "HttpOnly, Secure and SameSite=Lax", setc)
    r = mallory.post_json("/signin/webauthn/finish", {"credential": asserted})
    check(r.status == 401 and not r.cookie("__Host-pyle"), "a replayed assertion is refused",
          repr(r))
    r = browser.get("/account")
    check(r.status == 200 and a.user in r.text, "the account page answers with the session",
          repr(r))
    check("e2e passkey" in r.text, "and lists the passkey by its name")

    # ------------------------------------------------------------ OIDC
    section("OpenID Connect: authorization code with PKCE")
    r = rp.get("/.well-known/openid-configuration")
    disco = r.json()
    check(r.status == 200 and disco.get("issuer") == a.issuer, "discovery names the issuer",
          repr(r))
    check(disco.get("code_challenge_methods_supported") == ["S256"], "and S256 only",
          repr(disco.get("code_challenge_methods_supported")))
    check(disco.get("authorization_response_iss_parameter_supported") is True,
          "and RFC 9207's iss")
    r = rp.get("/jwks")
    jwks = r.json().get("keys", [])
    check(r.status == 200 and any(k.get("kty") == "EC" for k in jwks), "/jwks publishes an EC key",
          repr(r))

    verifier = b64u(os.urandom(32))
    challenge = b64u(hashlib.sha256(verifier.encode()).digest())
    nonce = b64u(os.urandom(12))

    def authorize_url(state, chal=challenge, scope="openid profile groups"):
        return "/authorize?" + urllib.parse.urlencode({
            "response_type": "code", "client_id": a.client, "redirect_uri": a.redirect,
            "scope": scope, "state": state, "nonce": nonce,
            "code_challenge": chal, "code_challenge_method": "S256"})

    stranger = Client("127.0.0.1", a.port, origin, "198.51.100.66")
    r = stranger.get(authorize_url("s0"))
    check(r.status in (302, 303) and r.location.startswith("/signin?"),
          "an authorization request without a session goes to sign in", repr(r))
    check(query_of(r.location).get("return", "").startswith("/authorize?"),
          "and comes back to the request", r.location)
    r = browser.get(authorize_url("s1").replace("code_challenge_method=S256",
                                                "code_challenge_method=plain"))
    loc = r.location
    check(r.status in (302, 303) and query_of(loc).get("error") == "invalid_request"
          or r.status == 400, "plain PKCE is refused", repr(r) + " " + loc)
    r = browser.get(authorize_url("s1"))
    loc = r.location
    q = query_of(loc)
    check(r.status in (302, 303) and loc.startswith(a.redirect + "?"),
          "with the session, back to the client", repr(r) + " " + loc)
    check(q.get("state") == "s1" and q.get("iss") == a.issuer and q.get("code"),
          "with the code, the state and iss", loc)
    code = q.get("code", "")

    def token(form, auth=True):
        return rp.post_form("/token", form, origin=False,
                            headers=basic(a.client, a.secret) if auth else {}, cookies=False)

    r = token({"grant_type": "authorization_code", "code": code, "redirect_uri": a.redirect,
               "code_verifier": b64u(os.urandom(32))})
    check(r.status == 400 and r.json().get("error") == "invalid_grant",
          "the wrong code_verifier is refused", repr(r))
    r = browser.get(authorize_url("s2"))
    code = query_of(r.location).get("code", "")
    r = token({"grant_type": "authorization_code", "code": code, "redirect_uri": a.redirect,
               "code_verifier": verifier}, auth=False)
    check(r.status == 401 and r.json().get("error") == "invalid_client",
          "a confidential client must authenticate", repr(r))
    r = browser.get(authorize_url("s3"))
    code = query_of(r.location).get("code", "")
    r = token({"grant_type": "authorization_code", "code": code, "redirect_uri": a.redirect,
               "code_verifier": verifier})
    tokens = r.json()
    check(r.status == 200 and tokens.get("token_type", "").lower() == "bearer",
          "the code is exchanged for tokens", repr(r))
    check(r.header("Cache-Control") == "no-store", "with Cache-Control: no-store",
          str(r.header("Cache-Control")))
    id_token = tokens.get("id_token", "")
    access = tokens.get("access_token", "")
    refresh = tokens.get("refresh_token", "")
    check(bool(id_token and access and refresh), "an ID token, an access token, a refresh token")
    r = token({"grant_type": "authorization_code", "code": code, "redirect_uri": a.redirect,
               "code_verifier": verifier})
    check(r.status == 400 and r.json().get("error") == "invalid_grant",
          "a code is good once", repr(r))
    r = token({"grant_type": "refresh_token", "refresh_token": refresh})
    check(r.status == 400 and r.json().get("error") == "invalid_grant",
          "and presenting it again revokes the refresh tokens it gave", repr(r))

    section("OpenID Connect: the ID token against /jwks")
    sub = None
    try:
        header, claims, signed, sig = jwt_parts(id_token)
        jwk = next((k for k in jwks if k.get("kid") == header.get("kid")), None)
        check(header.get("alg") == "ES256" and jwk is not None,
              "the ID token is ES256 under a published kid", repr(header))
        valid = jwk is not None and es256_verify(int.from_bytes(unb64u(jwk["x"]), "big"),
                                                 int.from_bytes(unb64u(jwk["y"]), "big"),
                                                 signed, sig)
        check(valid, "its signature verifies")
        tampered = json.dumps(dict(claims, sub="someone-else")).encode()
        forged = (id_token.split(".")[0] + "." + b64u(tampered)).encode()
        check(jwk is not None and not es256_verify(
            int.from_bytes(unb64u(jwk["x"]), "big"), int.from_bytes(unb64u(jwk["y"]), "big"),
            forged, sig), "and would not over altered claims")
        now = time.time()
        check(claims.get("iss") == a.issuer and claims.get("aud") in (a.client, [a.client]),
              "iss and aud", repr(claims))
        check(claims.get("nonce") == nonce, "the nonce comes back", repr(claims.get("nonce")))
        check(claims.get("iat", 0) <= now + 5 < claims.get("exp", 0) + 5
              and claims.get("auth_time", 0) <= now + 5, "iat, exp and auth_time", repr(claims))
        check(claims.get("acr") == "phrh" and "hwk" in claims.get("amr", []),
              "acr phrh and amr hwk", repr(claims))
        check(claims.get("pyle_account_acr") == "phrh", "and the account's level",
              repr(claims.get("pyle_account_acr")))
        check(claims.get("name") == a.user and claims.get("groups") == ["admin"],
              "name and groups, as the scopes allow", repr(claims))
        sub = claims.get("sub")
    except (ValueError, KeyError) as e:
        bad("the ID token is a JWT", str(e))

    section("userinfo with the biscuit")
    r = rp.get("/userinfo", headers={"Authorization": "Bearer " + access}, cookies=False)
    info = r.json()
    check(r.status == 200 and info.get("sub") == sub and sub,
          "userinfo answers for the ID token's subject", repr(r))
    check(info.get("groups") == ["admin"] and info.get("name") == a.user,
          "with name and groups", repr(info))
    r = rp.request("POST", "/userinfo", headers={"Authorization": "Bearer " + access},
                   cookies=False)
    check(r.status == 200 and r.json().get("sub") == sub, "POST /userinfo too", repr(r))
    raw = bytearray(unb64u(access))
    raw[len(raw) // 2] ^= 1
    r = rp.get("/userinfo", headers={"Authorization": "Bearer " + b64u(bytes(raw))},
               cookies=False)
    check(r.status == 401, "an altered biscuit is refused", repr(r))
    check("invalid_token" in (r.header("WWW-Authenticate") or ""),
          "with WWW-Authenticate: invalid_token", str(r.header("WWW-Authenticate")))
    r = rp.get("/userinfo", cookies=False)
    check(r.status == 401, "no token, no userinfo", repr(r))
    r = rp.get("/biscuit/keys")
    bkeys = r.json().get("keys", [])
    check(r.status == 200 and bkeys and all(k.get("public_key", "").startswith("ed25519/")
                                            for k in bkeys),
          "/biscuit/keys publishes Ed25519 roots", repr(r))

    section("refresh rotation and reuse")
    r = browser.get(authorize_url("s4"))
    r = token({"grant_type": "authorization_code", "code": query_of(r.location).get("code", ""),
               "redirect_uri": a.redirect, "code_verifier": verifier})
    refresh = r.json().get("refresh_token", "")
    check(r.status == 200 and refresh, "a fresh grant", repr(r))
    r = token({"grant_type": "refresh_token", "refresh_token": refresh})
    t2 = r.json()
    refresh2 = t2.get("refresh_token", "")
    check(r.status == 200 and refresh2 and refresh2 != refresh, "the refresh token rotates",
          repr(r))
    check(bool(t2.get("access_token")) and t2.get("access_token") != access,
          "and gives a new access token")
    r = token({"grant_type": "refresh_token", "refresh_token": refresh2, "scope": "openid"})
    t3 = r.json()
    refresh3 = t3.get("refresh_token", "")
    check(r.status == 200 and refresh3, "a refresh may narrow the scope", repr(r))
    r = rp.get("/userinfo", headers={"Authorization": "Bearer " + t3.get("access_token", "")},
               cookies=False)
    check(r.status == 200 and "groups" not in r.json(), "and the narrowed token says less",
          repr(r))
    r = token({"grant_type": "refresh_token", "refresh_token": refresh3,
               "scope": "openid offline_access"})
    check(r.status == 400 and r.json().get("error") == "invalid_scope",
          "but not beyond what was granted", repr(r))
    r = token({"grant_type": "refresh_token", "refresh_token": refresh})
    check(r.status == 400 and r.json().get("error") == "invalid_grant",
          "reusing a spent refresh token is refused", repr(r))
    r = token({"grant_type": "refresh_token", "refresh_token": refresh3})
    check(r.status == 400 and r.json().get("error") == "invalid_grant",
          "and revokes the whole family", repr(r))

    # A family for the logout section to end.
    r = browser.get(authorize_url("s5"))
    r = token({"grant_type": "authorization_code", "code": query_of(r.location).get("code", ""),
               "redirect_uri": a.redirect, "code_verifier": verifier})
    bound = r.json()
    check(r.status == 200 and bound.get("refresh_token"), "a second sign-in to the client",
          repr(r))

    # ------------------------------------------------------------ device grant
    section("device grant")
    device = Client("127.0.0.1", a.port, origin, "198.51.100.2")
    r = device.post_form("/device_authorization", {"client_id": a.public_client,
                                                   "scope": "openid groups"},
                         origin=False, cookies=False)
    d = r.json()
    check(r.status == 200 and d.get("device_code") and d.get("user_code"),
          "a device asks for a code", repr(r))
    check(d.get("verification_uri") == a.issuer + "/device", "to be entered at /device",
          repr(d.get("verification_uri")))
    user_code = d.get("user_code", "")
    interval = d.get("interval", 1)

    def poll():
        return device.post_form("/token", {"grant_type":
                                           "urn:ietf:params:oauth:grant-type:device_code",
                                           "device_code": d.get("device_code", ""),
                                           "client_id": a.public_client},
                                origin=False, cookies=False)

    r = poll()
    check(r.json().get("error") == "authorization_pending", "polling: authorization_pending",
          repr(r))
    r = poll()
    check(r.json().get("error") == "slow_down", "too fast: slow_down", repr(r))
    interval += 5
    page = "/device?" + urllib.parse.urlencode({"user_code": user_code})
    r = stranger.get(page)
    check(r.status in (302, 303) and "acr=phr" in r.location,
          "the page asks a stranger for a passkey", repr(r) + " " + r.location)
    r = browser.get(page)
    check(r.status == 200 and 'value="approve"' in r.text, "the page offers to approve",
          repr(r))
    r = browser.post_form("/device", {"user_code": user_code, "decision": "approve"},
                          headers={"Origin": "http://evil.example"})
    check(r.status == 403, "a cross-site approval is refused", repr(r))
    r = browser.post_form("/device", {"user_code": user_code, "decision": "approve"})
    check(r.status == 200, "the user approves", repr(r))
    time.sleep(interval + 0.5)
    r = poll()
    dt = r.json()
    check(r.status == 200 and dt.get("access_token") and dt.get("id_token"),
          "the device gets its tokens", repr(r))
    r = rp.get("/userinfo", headers={"Authorization": "Bearer " + dt.get("access_token", "")},
               cookies=False)
    check(r.status == 200 and r.json().get("sub") == sub, "for the same user", repr(r))
    time.sleep(interval + 0.5)
    r = poll()
    check(r.status == 400 and r.json().get("error") in ("invalid_grant", "expired_token"),
          "and only once", repr(r))
    device_refresh = dt.get("refresh_token", "")

    # ------------------------------------------------------------ forward auth
    section("forward authentication")
    proxy = Client("127.0.0.1", a.port, origin, "127.0.0.1")

    def ask(uri, host=a.fa_host, method="GET", cookies=(), secret=a.fa_secret):
        h = {"X-Forwarded-Host": host, "X-Forwarded-Uri": uri, "X-Forwarded-Method": method,
             "X-Forwarded-Proto": "https"}
        if secret:
            h["X-Pyle-Forward-Auth"] = secret
        if cookies:
            h["Cookie"] = "; ".join(cookies)
        return proxy.get("/forward-auth", headers=h, cookies=False)

    r = ask("/reports?q=1", secret=None)
    check(r.status == 403, "without the proxy's secret, refused", repr(r))
    r = ask("/reports?q=1", secret="x" * len(a.fa_secret))
    check(r.status == 403, "with a wrong secret, refused", repr(r))
    r = ask("/", host="elsewhere.example")
    check(r.status == 403, "a host not listed is refused", repr(r))
    r = ask("/api", method="POST")
    check(r.status == 401, "a POST without a cookie: 401", repr(r))
    begun = ask("/reports?q=1")
    state = begun.cookie("__Host-pyle-forward-state")
    check(begun.status == 302 and begun.location.startswith(a.issuer + "/forward-auth/grant?"),
          "no cookie: to the grant", repr(begun) + " " + begun.location)
    check(query_of(begun.location).get("rd") == f"https://{a.fa_host}/reports?q=1",
          "with the original URL", begun.location)
    check(bool(state), "and a state cookie on the protected host")
    r = stranger.get(path_of(begun.location))
    check(r.status in (302, 303) and r.location.startswith("/signin?"),
          "the grant sends a stranger to sign in", repr(r))
    g = browser.get(path_of(begun.location))
    cb = g.location
    check(g.status in (302, 303) and cb.startswith(f"https://{a.fa_host}/.pyle/forward-auth?code="),
          "the grant sends the browser back with a code", repr(g) + " " + cb)
    r = ask(path_of(cb))
    check(r.status == 403 and not r.cookie("__Host-pyle-forward"),
          "the code without the state cookie is refused", repr(r))
    begun = ask("/reports?q=1")
    state = begun.cookie("__Host-pyle-forward-state")
    cb = browser.get(path_of(begun.location)).location
    r = ask(path_of(cb), cookies=[f"__Host-pyle-forward-state={state}"])
    fwd = r.cookie("__Host-pyle-forward")
    check(r.status == 302 and r.location == "/reports?q=1",
          "the callback goes back to where the user was going", repr(r) + " " + r.location)
    check(bool(fwd), "and sets the host's cookie")
    r = ask(path_of(cb), cookies=[f"__Host-pyle-forward-state={state}"])
    check(not r.cookie("__Host-pyle-forward"), "a code is good once", repr(r))
    fcookie = [f"__Host-pyle-forward={fwd}"]
    r = ask("/reports", cookies=fcookie)
    check(r.status == 200 and r.header("Remote-User") == a.user,
          "with the cookie: 200 and Remote-User", repr(r))
    check(r.header("Remote-Groups") == "admin", "and Remote-Groups", str(r.header("Remote-Groups")))
    r = ask("/admin/x", cookies=fcookie)
    check(r.status == 403, "the host's policy still decides (/admin)", repr(r))
    r = ask("/x/../%61dmin/x", cookies=fcookie)
    check(r.status == 403, "however the path is spelled", repr(r))
    r = ask("/a%2Fb", cookies=fcookie)
    check(r.status == 400, "and a path pyle cannot read the service's way is 400", repr(r))
    r = ask("/", host=a.fa_other, cookies=fcookie)
    check(r.status == 302 and r.location.startswith(a.issuer + "/forward-auth/grant?"),
          "the cookie is for its host only: another protected host sends to the grant",
          repr(r) + " " + r.location)

    # ------------------------------------------------------------ logout
    section("end_session")
    bye = a.post_logout
    q = urllib.parse.urlencode({"id_token_hint": bound.get("id_token", ""),
                                "post_logout_redirect_uri": bye, "state": "x1"})
    r = browser.get("/end_session?" + q)
    check(r.status == 200 and 'action="/end_session/confirm"' in r.text,
          "logout asks before signing out", repr(r))
    r = browser.get("/end_session?" + urllib.parse.urlencode(
        {"client_id": a.client, "post_logout_redirect_uri": "https://evil.example/"}))
    check(r.status == 400 and not r.location, "an unregistered return address is refused",
          repr(r))
    r = browser.post_form("/end_session/confirm", {"client_id": a.client,
                                                   "post_logout_redirect_uri": bye,
                                                   "state": "x1"},
                          headers={"Origin": "http://evil.example"})
    check(r.status == 403, "a cross-site confirmation is refused", repr(r))
    r = browser.post_form("/end_session/confirm", {"client_id": a.client,
                                                   "post_logout_redirect_uri": bye,
                                                   "state": "x1"})
    check(r.status == 200 and f'href="{bye}?state=x1"' in r.text,
          "confirming links back to the client with the state", repr(r))
    check("__Host-pyle" not in browser.cookies, "and clears the session cookie")
    browser.cookies["__Host-pyle"] = session
    r = browser.get("/account")
    check(r.status in (302, 303), "the old session cookie is worthless", repr(r))
    r = token({"grant_type": "refresh_token", "refresh_token": bound.get("refresh_token", "")})
    check(r.json().get("error") == "invalid_grant", "the session's refresh tokens are revoked",
          repr(r))
    r = ask("/reports", cookies=fcookie)
    check(r.status == 302, "and the protected host's cookie with them", repr(r))
    r = device.post_form("/token", {"grant_type": "refresh_token",
                                    "refresh_token": device_refresh,
                                    "client_id": a.public_client},
                         origin=False, cookies=False)
    check(r.status == 200, "while the device's tokens, not tied to the session, live on",
          repr(r))
    r = browser.get("/end_session?" + q)
    check(r.status in (302, 303) and r.location == f"{bye}?state=x1",
          "without a session, logout goes straight back", repr(r) + " " + r.location)


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--port", type=int, required=True)
    p.add_argument("--issuer", required=True)
    p.add_argument("--invite", required=True)
    p.add_argument("--user", required=True)
    p.add_argument("--client", required=True)
    p.add_argument("--secret", required=True)
    p.add_argument("--redirect", required=True)
    p.add_argument("--post-logout", required=True)
    p.add_argument("--public-client", required=True)
    p.add_argument("--fa-host", required=True)
    p.add_argument("--fa-other", required=True)
    p.add_argument("--fa-secret", required=True)
    p.add_argument("--counts", required=True)
    a = p.parse_args()
    try:
        run(a)
    except Exception as e:  # noqa: BLE001 -- a crash is one more failure, not a traceback
        import traceback
        traceback.print_exc()
        bad("the run finished", f"{type(e).__name__}: {e}")
    with open(a.counts, "w") as f:
        f.write(f"{PASS} {FAIL}")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())