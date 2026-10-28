#!/usr/bin/env bash
# End to end: a real `pyle serve` on a free port, driven over HTTP.
#
# Everything happens in a temporary directory, over plain HTTP on localhost --
# which pyle accepts as an issuer for development -- so the test needs no
# certificate and touches nothing of the invoking user's.  The administrative
# steps are the real commands; the browser, the passkey, the OpenID Connect
# clients, the device and the reverse proxy are scripts/e2e.py, which uses the
# Python standard library only.
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d)"
PYLE="$ROOT/.lake/build/bin/pyle"

PASS=0; FAIL=0
ok()   { PASS=$((PASS+1)); printf '  ok   %s\n' "$1"; }
bad()  { FAIL=$((FAIL+1)); printf '  FAIL %s\n' "$1"; [ $# -gt 1 ] && printf '       %s\n' "$2"; }
check(){ if [ "$1" = "0" ]; then ok "$2"; else bad "$2" "${3:-}"; fi; }

cleanup() {
  [ -n "${PYLE_PID:-}" ] && kill "$PYLE_PID" 2>/dev/null
  rm -rf "$WORK"
}
trap cleanup EXIT

free_port() { python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1]);s.close()'; }

echo "== build"
(cd "$ROOT" && lake build pyle) > "$WORK/build.log" 2>&1
check $? "lake build pyle" "$(tail -20 "$WORK/build.log")"
[ -x "$PYLE" ] || { echo "no pyle binary at $PYLE"; exit 1; }

PORT="$(free_port)"
ISSUER="http://localhost:$PORT"
FA_HOST="app.localhost"
FA_OTHER="wiki.localhost"
FA_SECRET="forward-auth-secret-$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
REDIRECT="http://127.0.0.1:9/callback"
BYE="http://127.0.0.1:9/bye"
export PYLE_CONFIG="$WORK/pyle.json"

# ---------------------------------------------------------------- config
cat > "$PYLE_CONFIG" <<EOF
{
  "issuer": "$ISSUER",
  "rpId": "localhost",
  "origins": ["$ISSUER"],
  "port": $PORT,
  "database": "data/pyle.db",
  "rootKeyFile": "data/root.key",
  "trustedProxies": ["127.0.0.1"],
  "devicePollSeconds": 1,
  "forwardAuthSecret": "$FA_SECRET",
  "forwardAuthHosts": {
    "$FA_HOST": "deny if path(\$p), \$p.starts_with(\"/admin\");\nallow if group(\"admin\");",
    "$FA_OTHER": "allow if user(\$u);"
  }
}
EOF

echo
echo "== first run"
grep -v '"forwardAuthSecret"' "$PYLE_CONFIG" > "$WORK/nosecret.json"
OUT="$("$PYLE" user list --config "$WORK/nosecret.json" 2>&1)"
[ $? -ne 0 ] && grep -q "needs 'forwardAuthSecret'" <<< "$OUT"
check $? "forward-auth hosts without the proxy's secret are refused" "$OUT"
"$PYLE" init > "$WORK/init.log" 2>&1
check $? "pyle init" "$(cat "$WORK/init.log")"
MODE="$(stat -c '%a' "$WORK/data/root.key" 2>/dev/null)"
[ "$MODE" = "600" ]; check $? "the root key is mode 0600" "got $MODE"
SIZE="$(stat -c '%s' "$WORK/data/root.key" 2>/dev/null)"
[ "$SIZE" = "32" ]; check $? "and 32 bytes" "got $SIZE"
"$PYLE" init > "$WORK/init2.log" 2>&1
[ $? -ne 0 ]; check $? "a second init does not replace it" "$(cat "$WORK/init2.log")"
MODE="$(stat -c '%a' "$WORK/data/pyle.db" 2>/dev/null)"
[ "$MODE" = "600" ]; check $? "the database is mode 0600" "got $MODE"

"$PYLE" keys rotate > "$WORK/rotate.log" 2>&1
check $? "pyle keys rotate" "$(cat "$WORK/rotate.log")"
"$PYLE" keys list > "$WORK/keys.log" 2>&1
for use in es256 rs256 biscuit; do
  grep -q "^$use	current" "$WORK/keys.log"
  check $? "a current $use key" "$(cat "$WORK/keys.log")"
done

INVITE="$("$PYLE" invite alice --group admin --ttl 1h 2>"$WORK/invite.err")"
check $? "pyle invite alice --group admin" "$(cat "$WORK/invite.err")"
case "$INVITE" in "$ISSUER/invite/"*) ok "the link is on the issuer";; *) bad "the link is on the issuer" "$INVITE";; esac

"$PYLE" client add app --name App --redirect "$REDIRECT" --post-logout "$BYE" \
  > "$WORK/client.log" 2>&1
check $? "pyle client add app" "$(cat "$WORK/client.log")"
SECRET="$(tail -1 "$WORK/client.log")"
[ -n "$SECRET" ] && ! grep -qF -- "$SECRET" "$WORK/data/pyle.db"
check $? "the secret is printed and only its hash kept"
"$PYLE" client add tv --public --name TV --redirect "http://127.0.0.1/cb" > "$WORK/tv.log" 2>&1
check $? "pyle client add tv --public" "$(cat "$WORK/tv.log")"
"$PYLE" client add vault --name Vault --redirect "$REDIRECT" --min-acr phr > "$WORK/vault.log" 2>&1
check $? "pyle client add vault --min-acr phr" "$(cat "$WORK/vault.log")"
for LEVEL in gold sfa https://refeds.org/profile/sfa; do
  OUT="$("$PYLE" client add odd --redirect "$REDIRECT" --min-acr "$LEVEL" 2>&1)"
  [ $? -ne 0 ] && grep -q "is not a level" <<< "$OUT"
  check $? "--min-acr $LEVEL is refused" "$OUT"
done
CLIENTS="$("$PYLE" client list 2>&1)"
grep -q "^app	confidential	ES256	min-acr: mfa" <<< "$CLIENTS"
check $? "pyle client list, with the mfa floor by default" "$CLIENTS"
grep -q "^vault	confidential	ES256	min-acr: phr" <<< "$CLIENTS"
check $? "and the minimum given" "$CLIENTS"

# ---------------------------------------------------------------- the server
"$PYLE" serve > "$WORK/pyle.log" 2>&1 &
PYLE_PID=$!
for _ in $(seq 100); do
  curl -s -o /dev/null "http://127.0.0.1:$PORT/healthz" && break
  sleep 0.1
done

echo
echo "== the server"
OUT="$(curl -s "http://127.0.0.1:$PORT/healthz")"
[ "$OUT" = '{"status":"ok"}' ]; check $? "/healthz answers" "$OUT"
grep -q "listening on 127.0.0.1:$PORT as $ISSUER" "$WORK/pyle.log"
check $? "pyle serve says where it listens" "$(cat "$WORK/pyle.log")"
HDRS="$(curl -s -D - -o /dev/null "http://127.0.0.1:$PORT/healthz")"
grep -qi "^content-security-policy: .*frame-ancestors 'none'" <<< "$HDRS"
check $? "every reply carries the CSP" "$HDRS"
grep -qi "^referrer-policy: no-referrer" <<< "$HDRS"
check $? "and Referrer-Policy" "$HDRS"
CODE="$(curl -s -o /dev/null -w '%{http_code}' "http://127.0.0.1:$PORT/nothing-here")"
[ "$CODE" = "404" ]; check $? "an unknown path is 404" "got $CODE"
for P in /forward-auth/ //forward-auth /forward-auth// /forward-auth/grant/; do
  CODE="$(curl -s -o /dev/null -w '%{http_code}' --path-as-is -H "X-Pyle-Forward-Auth: $FA_SECRET" \
    -H "X-Forwarded-Host: $FA_HOST" -H "X-Forwarded-Uri: /" "http://127.0.0.1:$PORT$P")"
  [ "$CODE" = "404" ]; check $? "$P is not the forward-auth check" "got $CODE"
done
CODE="$(curl -s -o /dev/null -w '%{http_code}' -X POST -H "Origin: http://evil.example" \
  "http://127.0.0.1:$PORT/logout")"
[ "$CODE" = "403" ]; check $? "a cross-origin POST is refused" "got $CODE"
CODE="$(curl -s -o /dev/null -w '%{http_code}' -X POST -H "Origin: $ISSUER" \
  -H 'Content-Type: application/json' --data-binary @<(head -c 100000 /dev/zero | tr '\0' a) \
  "http://127.0.0.1:$PORT/signin/webauthn/begin")"
[ "$CODE" = "413" ]; check $? "an oversized body is refused" "got $CODE"

python3 -I "$ROOT/scripts/e2e.py" --port "$PORT" --issuer "$ISSUER" --invite "$INVITE" \
  --user alice --client app --secret="$SECRET" --redirect "$REDIRECT" --post-logout "$BYE" \
  --public-client tv --fa-host "$FA_HOST" --fa-other "$FA_OTHER" \
  --fa-secret="$FA_SECRET" --counts "$WORK/counts"
if [ -f "$WORK/counts" ]; then
  read -r P F < "$WORK/counts"
  PASS=$((PASS+P)); FAIL=$((FAIL+F))
else
  bad "scripts/e2e.py reported its counts"
fi

echo
echo "== afterwards"
USERS="$("$PYLE" user list 2>&1)"
# Her passkey, and the one of her two authenticator apps the run left.
grep -q "^alice	groups: admin	authenticators: 2" <<< "$USERS"
check $? "pyle user list shows alice, her passkey and her authenticator app" "$USERS"
grep -q "^alice	.*	email: -	display name: -" <<< "$USERS"
check $? "and no email address or display name yet" "$USERS"
OUT="$("$PYLE" user set alice --email Alice@Example.org --display-name "Alice Example" 2>&1)"
check $? "pyle user set alice --email --display-name" "$OUT"
USERS="$("$PYLE" user list 2>&1)"
grep -q "^alice	.*	email: Alice@Example.org	display name: Alice Example$" <<< "$USERS"
check $? "pyle user list shows them" "$USERS"
OUT="$("$PYLE" user add bob --email alice@example.ORG 2>&1)"
[ $? -ne 0 ] && grep -q "already used by the account 'alice'" <<< "$OUT"
check $? "another account cannot have her address in another case" "$OUT"
OUT="$("$PYLE" user set alice --email a@b.org --no-email 2>&1)"
[ $? -eq 2 ]; check $? "--email and --no-email together are refused" "$OUT"
OUT="$("$PYLE" user set alice --email not-an-address 2>&1)"
[ $? -ne 0 ] && grep -q "not an acceptable email address" <<< "$OUT"
check $? "so is an address without an @" "$OUT"
OUT="$("$PYLE" user set alice --no-display-name 2>&1)"
check $? "pyle user set alice --no-display-name" "$OUT"
grep -q "^alice	.*	email: Alice@Example.org	display name: -$" <<< "$("$PYLE" user list 2>&1)"
check $? "clears only the display name"
OUT="$("$PYLE" user set alice --email "alice@exÄmple.org" 2>&1)"
[ $? -ne 0 ] && grep -q "email addresses must be ASCII" <<< "$OUT"
check $? "a non-ASCII address is refused" "$OUT"
OUT="$("$PYLE" user set alice --email alice@new.example.org --display-name $'Al‮ice' 2>&1)"
[ $? -ne 0 ] && grep -q "^alice	.*	email: Alice@Example.org	display name: -$" \
  <<< "$("$PYLE" user list 2>&1)"
check $? "a bad display name beside a good address changes neither" "$OUT"
for ARGS in "user add bob --no-email" "invite bob --no-display-name" \
    "user list --email a@b.org" "client list --display-name x"; do
  OUT="$("$PYLE" $ARGS 2>&1)"
  [ $? -eq 2 ]; check $? "pyle $ARGS is refused" "$OUT"
done
"$PYLE" user set alice --email alice@new.example.org > /dev/null 2>&1
cat "$WORK"/data/pyle.db* | grep -aqF "email: none -> Alice@Example.org" &&
  cat "$WORK"/data/pyle.db* | grep -aqF "email: Alice@Example.org -> alice@new.example.org" &&
  cat "$WORK"/data/pyle.db* | grep -aqF 'display name: "Alice Example" -> none'
check $? "the audit log records the old and the new values"
kill -0 "$PYLE_PID" 2>/dev/null
check $? "the server is still running"
# Only the oversized body above may have failed a connection.
CONN="$(grep "pyle: connection" "$WORK/pyle.log" | grep -v "Entity too large")"
[ -z "$CONN" ]; check $? "and logged no connection failures" "$CONN"
OUT="$("$PYLE" audit verify 2>&1)"
check $? "pyle audit verify" "$OUT"
grep -q "form an unbroken chain" <<< "$OUT"
check $? "the audit log is an unbroken chain" "$OUT"
grep -qF -- "$SECRET" "$WORK/data/pyle.db"
[ $? -ne 0 ]; check $? "the database never contains the client secret"

echo
if [ "$FAIL" -eq 0 ]; then
  echo "$PASS checks passed"
  exit 0
else
  echo "$PASS passed, $FAIL FAILED"
  echo "--- pyle log ---"; tail -30 "$WORK/pyle.log"
  exit 1
fi