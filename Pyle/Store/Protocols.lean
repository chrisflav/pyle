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
  /-- When it stops being accepted. -/
  expires : Nat

/-- Record a forward-authentication code under its hash. -/
def Store.addForwardAuthCode (s : Store) (codeHash : SecretHash) (fc : ForwardAuthCode) :
    IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO forward_auth_codes (code_hash, session_hash, host, path, expires) \
      VALUES (?, ?, ?, ?, ?)"
    #[codeHash, fc.session, fc.host, fc.path, fc.expires]

/-- Consume a forward-authentication code: delete it and return it, if it
existed and had not expired at `now`. -/
def Store.consumeForwardAuthCode (s : Store) (codeHash : SecretHash) (now : Nat) :
    IO (Option ForwardAuthCode) := s.run fun c => do
  let row ← queryOne c
    "DELETE FROM forward_auth_codes WHERE code_hash = ? \
      RETURNING session_hash, host, path, expires"
    #[codeHash] fun st => do
      return { session := .ofStored (← colBlob st 0), host := ← colText st 1,
               path := ← colText st 2, expires := ← colNat st 3 : ForwardAuthCode }
  return row.filter (now < ·.expires)

/-- Remove expired forward-authentication codes; how many. -/
def Store.purgeForwardAuthCodes (s : Store) (now : Nat) : IO Nat := s.run fun c =>
  exec c "DELETE FROM forward_auth_codes WHERE expires <= ?" #[now]

end Store
end Pyle