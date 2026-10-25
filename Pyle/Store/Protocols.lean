import Pyle.Store.Oidc

/-!
# Queries for the protocols

What the OpenID Connect provider, the signing-key lifecycle and forward
authentication need of the store beyond `Pyle.Store.Oidc`: per-client settings
added by the second migration, per-algorithm key rotation, revoking a user's
refresh-token families for one client, and the one-time codes of forward
authentication.

The keys of the three uses — ES256 and RS256 for ID tokens, Ed25519 for the
biscuit root — share the `keys` table and are told apart by their algorithm,
so each rotates on its own (DESIGN.md §6.3).
-/

namespace Pyle
namespace Store

/-! ## Client settings -/

/-- What the second migration added to a client. -/
structure ClientSettings where
  /-- The JOSE algorithm its ID tokens are signed with: `ES256` or `RS256`. -/
  idTokenAlg : String := "ES256"
  /-- Where RP-initiated logout may send the browser afterwards, compared byte
  for byte. -/
  postLogoutRedirectUris : List String := []
  deriving Inhabited, BEq, Repr

/-- A client's settings, if the client exists. -/
def Store.clientSettings (s : Store) (id : String) : IO (Option ClientSettings) :=
  s.run fun c => queryOne c
    "SELECT id_token_alg, post_logout_redirect_uris FROM clients WHERE id = ?" #[id]
    fun st => return { idTokenAlg := ← colText st 0, postLogoutRedirectUris := ← colList st 1 }

/-- Replace a client's settings.  Whether the client exists. -/
def Store.setClientSettings (s : Store) (id : String) (cs : ClientSettings) : IO Bool :=
  s.run fun c => return (← exec c
    "UPDATE clients SET id_token_alg = ?, post_logout_redirect_uris = ? WHERE id = ?"
    #[cs.idTokenAlg, encodeList cs.postLogoutRedirectUris, id]) > 0

/-! ## Keys by algorithm -/

/-- Read a key row selected as `keyColumns` lists. -/
private def readKeyRow (st : SQLite.Stmt) : IO StoredKey := do
  let stateName ← colText st 2
  let some state := KeyState.ofString? stateName
    | throw (.userError s!"store: unknown key state '{stateName}'")
  return { kid := ← colText st 0, algorithm := ← colText st 1, state,
           sealedKey := ← colBlob st 3, publicKey := ← colBlob st 4, created := ← colNat st 5 }

/-- The columns `readKeyRow` reads. -/
private def keyColumns : String := "kid, algorithm, state, sealed, public_key, created"

/-- The keys of one algorithm that are not retired, newest first. -/
def Store.keysOf (s : Store) (algorithm : String) : IO (Array StoredKey) := s.run fun c =>
  query c s!"SELECT {keyColumns} FROM keys WHERE algorithm = ? AND state != 'retired' \
    ORDER BY created DESC, kid" #[algorithm] readKeyRow

/-- Every key, retired ones included, by algorithm and then newest first; for
`pyle keys list`. -/
def Store.allKeys (s : Store) : IO (Array StoredKey) := s.run fun c =>
  query c s!"SELECT {keyColumns} FROM keys ORDER BY algorithm, created DESC, kid" #[] readKeyRow

/-- Rotate the keys of one algorithm: its current key becomes previous, its
previous one retired, and its next key `kid` current, in one transaction.
Keys of other algorithms are untouched.  Whether `kid` was that algorithm's
next key. -/
def Store.promoteKeyOf (s : Store) (algorithm kid : String) : IO Bool :=
  s.atomically fun c => do
    let isNext ← queryOne c
      "SELECT 1 FROM keys WHERE kid = ? AND algorithm = ? AND state = 'next'" #[kid, algorithm]
      (colInt · 0)
    if isNext.isNone then return false
    discard <| exec c
      "UPDATE keys SET state = 'retired' WHERE algorithm = ? AND state = 'previous'" #[algorithm]
    discard <| exec c
      "UPDATE keys SET state = 'previous' WHERE algorithm = ? AND state = 'current'" #[algorithm]
    discard <| exec c "UPDATE keys SET state = 'current' WHERE kid = ?" #[kid]
    return true

/-- Record a key as its algorithm's current one, if that algorithm has none
yet: the first key, made when pyle first needs one.  Whether it was recorded;
if two processes race, one key wins and the other is not stored. -/
def Store.addFirstKey (s : Store) (k : StoredKey) : IO Bool := s.atomically fun c => do
  let existing ← queryOne c
    "SELECT 1 FROM keys WHERE algorithm = ? AND state = 'current'" #[k.algorithm] (colInt · 0)
  if existing.isSome then return false
  discard <| exec c
    s!"INSERT INTO keys ({keyColumns}) VALUES (?, ?, 'current', ?, ?, ?)"
    #[k.kid, k.algorithm, k.sealedKey, k.publicKey, k.created]
  return true

/-! ## Refresh tokens by user and client -/

/-- Revoke every refresh-token family a user holds at one client, as
RP-initiated logout does: delete their tokens and record the families as
revoked.  How many families there were. -/
def Store.revokeUserClientFamilies (s : Store) (user : UserId) (clientId : String)
    (now : Nat) : IO Nat := s.atomically fun c => do
  let families ← query c
    "SELECT DISTINCT family FROM refresh_tokens WHERE user_id = ? AND client_id = ?"
    #[user, clientId] (colBlob · 0)
  for f in families do
    discard <| exec c "DELETE FROM refresh_tokens WHERE family = ?" #[f]
    discard <| exec c
      "INSERT OR IGNORE INTO revoked_families (family, revoked) VALUES (?, ?)" #[f, now]
  return families.size

/-- Whether a refresh-token family has tokens or has been revoked. -/
def Store.familyExists (s : Store) (family : ByteArray) : IO Bool := s.run fun c => do
  let row ← queryOne c
    "SELECT 1 FROM refresh_tokens WHERE family = ? \
      UNION ALL SELECT 1 FROM revoked_families WHERE family = ?"
    #[family, family] (colInt · 0)
  return row.isSome

/-! ## Forward-authentication codes -/

/-- What a forward-authentication code is bound to. -/
structure ForwardAuthCode where
  /-- The hash of the identifier of the session it was issued from. -/
  session : SecretHash
  /-- The protected host it may be redeemed at. -/
  host : String
  /-- The path and query to send the browser back to. -/
  path : String
  /-- The SHA-256 of the state cookie of the browser that asked for it. -/
  state : SecretHash
  /-- When it stops being accepted. -/
  expires : Nat

/-- Record a forward-authentication code under its hash. -/
def Store.addForwardAuthCode (s : Store) (codeHash : SecretHash) (fc : ForwardAuthCode) :
    IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO forward_auth_codes (code_hash, session_hash, host, path, state_hash, \
      expires) VALUES (?, ?, ?, ?, ?, ?)"
    #[codeHash, fc.session, fc.host, fc.path, fc.state, fc.expires]

/-- Consume a forward-authentication code: delete it and return it, if it
existed and had not expired at `now`. -/
def Store.consumeForwardAuthCode (s : Store) (codeHash : SecretHash) (now : Nat) :
    IO (Option ForwardAuthCode) := s.run fun c => do
  let row ← queryOne c
    "DELETE FROM forward_auth_codes WHERE code_hash = ? \
      RETURNING session_hash, host, path, state_hash, expires"
    #[codeHash] fun st => do
      return { session := .ofStored (← colBlob st 0), host := ← colText st 1,
               path := ← colText st 2, state := .ofStored (← colBlob st 3),
               expires := ← colNat st 4 : ForwardAuthCode }
  return row.filter (now < ·.expires)

/-- Remove expired forward-authentication codes; how many. -/
def Store.purgeForwardAuthCodes (s : Store) (now : Nat) : IO Nat := s.run fun c =>
  exec c "DELETE FROM forward_auth_codes WHERE expires <= ?" #[now]

/-- Remove expired authorization codes; how many.  A code is consumed by its
exchange, so these are the ones never exchanged. -/
def Store.purgeCodes (s : Store) (now : Nat) : IO Nat := s.run fun c =>
  exec c "DELETE FROM codes WHERE expires <= ?" #[now]

/-! ## Codes and refresh-token families tied to sessions -/

/-- Record which session an authorization code was issued from. -/
def Store.setCodeSession (s : Store) (codeHash session : SecretHash) : IO Unit :=
  s.run fun c => discard <| exec c "UPDATE codes SET session_hash = ? WHERE code_hash = ?"
    #[session, codeHash]

/-- The session an authorization code was issued from, read before the code is
consumed. -/
def Store.codeSession (s : Store) (codeHash : SecretHash) : IO (Option SecretHash) :=
  s.run fun c => do
    let row ← queryOne c "SELECT session_hash FROM codes WHERE code_hash = ?" #[codeHash]
      (colOpt colBlob · 0)
    return (row.bind id).map SecretHash.ofStored

/-- Record a new refresh-token family's absolute expiry and the session it is
tied to (`none` for an `offline_access` grant).  The triggers of the schema
move the tie when the session is rotated, and revoke the family when the
session ends.  A family whose session has already ended when it is recorded is
revoked at once, so nothing outlives the session it came from. -/
def Store.addRefreshFamily (s : Store) (family : ByteArray) (expires : Nat)
    (session : Option SecretHash) (now : Nat) : IO Unit := s.atomically fun c => do
  discard <| exec c
    "INSERT INTO refresh_families (family, expires, session_hash) VALUES (?, ?, ?)"
    #[family, expires, Value.opt session]
  if let some h := session then
    let live ← queryOne c "SELECT 1 FROM sessions WHERE id_hash = ?" #[h] (colInt · 0)
    if live.isNone then
      discard <| exec c "DELETE FROM refresh_tokens WHERE family = ?" #[family]
      discard <| exec c
        "INSERT OR IGNORE INTO revoked_families (family, revoked) VALUES (?, ?)" #[family, now]

/-- The absolute expiry of the family a refresh token belongs to, if it has
one: what rotation must not extend. -/
def Store.familyExpiry (s : Store) (tokenHash : SecretHash) : IO (Option Nat) := s.run fun c =>
  queryOne c
    "SELECT f.expires FROM refresh_tokens t JOIN refresh_families f ON f.family = t.family \
      WHERE t.token_hash = ?" #[tokenHash] (colNat · 0)

/-! ## Device codes, by client -/

/-- Poll with a device code on behalf of `clientId` (RFC 8628 §3.5), as
`Store.pollDeviceCode` does, with two differences: only a code issued to
`clientId` is touched, so a poll by another client changes and destroys
nothing; and polling too fast grows the code's interval by five seconds, as
§3.5 asks of `slow_down`.  `none` when the code exists but belongs to another
client. -/
def Store.pollDeviceCodeFor (s : Store) (deviceCodeHash : SecretHash) (clientId : String)
    (now : Nat) : IO (Option DevicePoll) := s.atomically fun c => do
  let decided ← queryOne c
    "DELETE FROM device_codes \
      WHERE device_code_hash = ? AND client_id = ? AND status IN ('approved', 'denied') \
      AND expires > ? \
      RETURNING status, client_id, scope, user_id, amr, auth_time"
    #[deviceCodeHash, clientId, now] fun st =>
      return (← colText st 0, ← colText st 1, ← colText st 2, ← colOpt colInt st 3,
        ← colList st 4, ← colOpt colNat st 5)
  match decided with
  | some ("approved", cid, scope, some user, amr, some authTime) =>
    return some (.approved cid scope ⟨user⟩ amr authTime)
  | some _ => return some .denied
  | none =>
    let pending ← queryOne c
      "SELECT interval, last_poll FROM device_codes \
        WHERE device_code_hash = ? AND client_id = ? AND status = 'pending' AND expires > ?"
      #[deviceCodeHash, clientId, now] fun st => return (← colNat st 0, ← colNat st 1)
    match pending with
    | some (interval, lastPoll) =>
      if lastPoll + interval > now then
        discard <| exec c
          "UPDATE device_codes SET last_poll = ?, interval = interval + 5 \
            WHERE device_code_hash = ?" #[now, deviceCodeHash]
        return some .slowDown
      discard <| exec c "UPDATE device_codes SET last_poll = ? WHERE device_code_hash = ?"
        #[now, deviceCodeHash]
      return some .pending
    | none =>
      let other ← queryOne c
        "SELECT 1 FROM device_codes WHERE device_code_hash = ? AND client_id != ?"
        #[deviceCodeHash, clientId] (colInt · 0)
      return if other.isSome then none else some .expired

end Store
end Pyle