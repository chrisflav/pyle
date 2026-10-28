import Pyle.Store.Sessions

/-!
# Clients, codes, tokens and keys

The state behind what services receive (DESIGN.md §5): registered OIDC
clients, authorization codes, refresh-token families, device codes, signing
keys, and the invitations accounts are created from.

Every bearer value here — a code, a refresh token, a device code, an
invitation — is stored as its SHA-256 and consumed atomically:

* a code by one `DELETE … RETURNING`, so it is good once (§5.1, §9.4);
* a refresh token by `rotateRefreshToken`, one transaction that marks it used
  and stores its successor, or revokes its whole family when the token
  presented was already used (§5.1), as `refreshDecision` decides; a revoked
  family is recorded, and the schema refuses any token added to one;
* a device code by `Store.pollDeviceCodeFor`, one transaction that reads it
  and deletes it once it has been decided, as `deviceDecision` decides;
* an invitation by `Store.redeemInvitation`, one transaction that reads it,
  checks it, and deletes it as it creates the account.

The binding checks (client, redirect URI, PKCE) belong to the OIDC modules;
the store returns the bound fields so that they can be checked, and makes sure
nothing is returned twice.
-/

namespace Pyle
namespace Store

/-! ## Clients -/

/-- A registered OIDC client. -/
structure Client where
  /-- The `client_id`. -/
  id : String
  /-- A name to show on the consent and sign-in pages. -/
  name : String
  /-- The SHA-256 of the client secret, for a confidential client; `none` for
  a public one.  PKCE is required either way (§5.1). -/
  secretHash : Option SecretHash
  /-- The redirect URIs, compared byte for byte. -/
  redirectUris : List String
  /-- The scopes it may ask for. -/
  scopes : List String
  /-- When it was registered. -/
  created : Nat

/-- The columns of `clients`, in the order `readClient` reads them. -/
def clientColumns : String := "id, name, secret_hash, redirect_uris, scopes, created"

/-- Read a client row selected with `clientColumns`. -/
def readClient (stmt : SQLite.Stmt) : IO Client := do
  return {
    id := ← colText stmt 0
    name := ← colText stmt 1
    secretHash := (← colOpt colBlob stmt 2).map SecretHash.ofStored
    redirectUris := ← colList stmt 3
    scopes := ← colList stmt 4
    created := ← colNat stmt 5 }

/-- Register a client, or replace the one with the same id. -/
def Store.putClient (s : Store) (cl : Client) : IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO clients (id, name, secret_hash, redirect_uris, scopes, created) \
      VALUES (?, ?, ?, ?, ?, ?) \
      ON CONFLICT (id) DO UPDATE SET name = excluded.name, secret_hash = excluded.secret_hash, \
      redirect_uris = excluded.redirect_uris, scopes = excluded.scopes"
    #[cl.id, cl.name, Value.opt cl.secretHash, encodeList cl.redirectUris,
      encodeList cl.scopes, cl.created]

/-- Look a client up by id. -/
def Store.findClient (s : Store) (id : String) : IO (Option Client) := s.run fun c =>
  queryOne c s!"SELECT {clientColumns} FROM clients WHERE id = ?" #[id] readClient

/-- Every client, by id. -/
def Store.listClients (s : Store) : IO (Array Client) := s.run fun c =>
  query c s!"SELECT {clientColumns} FROM clients ORDER BY id" #[] readClient

/-- Remove a client, and with it its codes and tokens.  Whether it existed. -/
def Store.removeClient (s : Store) (id : String) : IO Bool := s.run fun c => do
  return (← exec c "DELETE FROM clients WHERE id = ?" #[id]) > 0

/-! ## Authorization codes -/

/-- What an authorization code is bound to (§5.1). -/
structure AuthCode where
  /-- The client it was issued to. -/
  clientId : String
  /-- The redirect URI of the authorization request. -/
  redirectUri : String
  /-- The PKCE `S256` code challenge. -/
  codeChallenge : String
  /-- Who signed in. -/
  user : UserId
  /-- The granted scope, space-separated. -/
  scope : String
  /-- The `nonce` of the authorization request, for the ID token. -/
  nonce : Option String
  /-- The session's `amr`. -/
  amr : List String
  /-- The session's `auth_time`. -/
  authTime : Nat
  /-- When the code stops being accepted (60 s after issue). -/
  expires : Nat
  /-- The `acr` its ID tokens state, when the request asked for one as an
  essential claim (OpenID Connect Core §5.5.1.1); otherwise `none`, and they
  state the level the `amr` records. -/
  acr : Option String := none

/-- Record an issued code under its hash. -/
def Store.addCode (s : Store) (codeHash : SecretHash) (a : AuthCode) : IO Unit :=
  s.run fun c => do
    discard <| exec c
      "INSERT INTO codes (code_hash, client_id, redirect_uri, code_challenge, user_id, scope, \
        nonce, amr, auth_time, expires, acr) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
      #[codeHash, a.clientId, a.redirectUri, a.codeChallenge, a.user, a.scope,
        Value.opt a.nonce, encodeList a.amr, a.authTime, a.expires, Value.opt a.acr]

/-- Consume a code: delete it and return what it was bound to, if it existed
and had not expired at `now`.  An expired code is deleted all the same. -/
def Store.consumeCode (s : Store) (codeHash : SecretHash) (now : Nat) :
    IO (Option AuthCode) := s.run fun c => do
  let row ← queryOne c
    "DELETE FROM codes WHERE code_hash = ? RETURNING client_id, redirect_uri, code_challenge, \
      user_id, scope, nonce, amr, auth_time, expires, acr"
    #[codeHash] fun st => do
      return {
        clientId := ← colText st 0
        redirectUri := ← colText st 1
        codeChallenge := ← colText st 2
        user := ⟨← colInt st 3⟩
        scope := ← colText st 4
        nonce := ← colOpt colText st 5
        amr := ← colList st 6
        authTime := ← colNat st 7
        expires := ← colNat st 8
        acr := ← colOpt colText st 9 : AuthCode }
  return row.filter (now < ·.expires)

/-! ## Refresh tokens -/

/-- A refresh token's grant: what the next tokens are issued for. -/
structure RefreshGrant where
  /-- The family it belongs to: every token rotated from one sign-in. -/
  family : ByteArray
  /-- The client it was issued to. -/
  clientId : String
  /-- Whose it is. -/
  user : UserId
  /-- The granted scope. -/
  scope : String
  /-- The `amr` of the sign-in it descends from. -/
  amr : List String
  /-- The `auth_time` of that sign-in. -/
  authTime : Nat
  /-- When this token stops being accepted. -/
  expires : Nat
  /-- The `acr` the ID tokens of the grant state, if the authorization asked
  for one as an essential claim (`AuthCode.acr`). -/
  acr : Option String := none

/-- Insert a refresh token row.  Internal: a successor is only ever inserted by
`rotateRefreshToken`, in the transaction that used its predecessor, and the
first token of a family only by `startRefreshFamily`. -/
private def insertRefreshToken (c : SQLite) (tokenHash : SecretHash) (g : RefreshGrant)
    (now : Nat) : IO Unit := do
  discard <| exec c
    "INSERT INTO refresh_tokens (token_hash, family, client_id, user_id, scope, amr, auth_time, \
      created, expires, acr) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    #[tokenHash, g.family, g.clientId, g.user, g.scope, encodeList g.amr, g.authTime, now,
      g.expires, Value.opt g.acr]

/-- Issue the first refresh token of a new family, after a code exchange or a
device grant.  Refused if the family already has tokens or has been revoked:
a family is begun once.  (A trigger in the schema refuses any insert into a
revoked family as well.) -/
def Store.startRefreshFamily (s : Store) (tokenHash : SecretHash) (g : RefreshGrant)
    (now : Nat) : IO Unit := s.atomically fun c => do
  let used ← queryOne c
    "SELECT 1 FROM refresh_tokens WHERE family = ? \
      UNION ALL SELECT 1 FROM revoked_families WHERE family = ?"
    #[g.family, g.family] (colInt · 0)
  if used.isSome then throw (.userError "store: that refresh-token family is not new")
  insertRefreshToken c tokenHash g now

/-- What presenting a refresh token came to. -/
inductive RefreshOutcome where
  /-- The token was current for this client: it is now used, its successor
  has been stored, and here is the grant both carry. -/
  | rotated (grant : RefreshGrant)
  /-- The token had already been used: its whole family has been revoked. -/
  | reused
  /-- No such token for this client, or it has expired. -/
  | invalid

/-- A refresh-token row as rotation reads it: the grant it carries, when it
was used, if it was, and whether its family has been revoked. -/
structure RefreshRow where
  /-- The grant, with the token's own expiry. -/
  grant : RefreshGrant
  /-- When the token was used, if it was. -/
  usedAt : Option Nat
  /-- Whether its family is recorded in `revoked_families`. -/
  familyRevoked : Bool

/-- What presenting a refresh token is to do to the store. -/
inductive RefreshDecision where
  /-- Mark the token used and store its successor with this grant. -/
  | rotate (grant : RefreshGrant)
  /-- The token was used before: revoke this family. -/
  | revoke (family : ByteArray)
  /-- Change nothing: the token is unknown, another client's, expired, or of a
  revoked family. -/
  | invalid

/-- Decide what presenting a refresh token on behalf of `clientId` at `now`
comes to, given its row, if there is one; a successor would be valid until
`expires`.

* A token of another client is invalid, so one client cannot end another's
  sessions by replaying a value it should never have seen.
* A token used before revokes its family, whether or not it has expired since.
* An unused token is rotated if it has not expired and its family is not
  revoked; otherwise it is invalid. -/
def refreshDecision (row : Option RefreshRow) (clientId : String) (now expires : Nat) :
    RefreshDecision :=
  match row with
  | none => .invalid
  | some r =>
    if r.grant.clientId ≠ clientId then .invalid
    else if r.usedAt.isSome then .revoke r.grant.family
    else if r.familyRevoked ∨ ¬ now < r.grant.expires then .invalid
    else .rotate { r.grant with expires }

/-- Present refresh token `old` on behalf of `clientId`, and rotate it to
`new`, valid until `expires`.  One `BEGIN IMMEDIATE` transaction reads the
row of `old`, lets `refreshDecision` decide, and carries the decision out:

* `rotate`: mark `old` used and insert `new` in the same family — the
  successor exists exactly when its predecessor was used, and never in a
  revoked family;
* `revoke`: delete every token in the family and record the family as
  revoked, so nothing can be added to it afterwards;
* `invalid`: nothing changes. -/
def Store.rotateRefreshToken (s : Store) (old new : SecretHash) (clientId : String)
    (now expires : Nat) : IO RefreshOutcome := s.atomically fun c => do
  let row ← queryOne c
    "SELECT family, client_id, user_id, scope, amr, auth_time, expires, used_at, \
      EXISTS (SELECT 1 FROM revoked_families r WHERE r.family = refresh_tokens.family), acr \
      FROM refresh_tokens WHERE token_hash = ?"
    #[old] fun st => do
      return {
        grant := {
          family := ← colBlob st 0
          clientId := ← colText st 1
          user := ⟨← colInt st 2⟩
          scope := ← colText st 3
          amr := ← colList st 4
          authTime := ← colNat st 5
          expires := ← colNat st 6
          acr := ← colOpt colText st 9 }
        usedAt := ← colOpt colNat st 7
        familyRevoked := (← colInt st 8) != 0 : RefreshRow }
  match refreshDecision row clientId now expires with
  | .rotate g =>
    discard <| exec c "UPDATE refresh_tokens SET used_at = ? WHERE token_hash = ?" #[now, old]
    insertRefreshToken c new g now
    return .rotated g
  | .revoke f =>
    discard <| exec c "DELETE FROM refresh_tokens WHERE family = ?" #[f]
    discard <| exec c
      "INSERT OR IGNORE INTO revoked_families (family, revoked) VALUES (?, ?)" #[f, now]
    return .reused
  | .invalid => return .invalid

/-- Revoke a whole family, as RP-initiated logout or an administrator does:
delete its tokens and record it as revoked.  How many tokens it had. -/
def Store.revokeRefreshFamily (s : Store) (family : ByteArray) (now : Nat) : IO Nat :=
  s.atomically fun c => do
    let n ← exec c "DELETE FROM refresh_tokens WHERE family = ?" #[family]
    discard <| exec c
      "INSERT OR IGNORE INTO revoked_families (family, revoked) VALUES (?, ?)" #[family, now]
    return n

/-! ## Device codes (RFC 8628) -/

/-- The state of a device authorization. -/
inductive DeviceStatus where
  /-- Waiting for the user. -/
  | pending
  /-- Approved by `user`, with that session's `amr` and `auth_time`. -/
  | approved (user : UserId) (amr : List String) (authTime : Nat)
  /-- Refused by the user. -/
  | denied

/-- A device authorization as recorded. -/
structure DeviceCode where
  /-- The code the person types, short and unambiguous. -/
  userCode : String
  /-- The client asking. -/
  clientId : String
  /-- The scope asked for. -/
  scope : String
  /-- The minimum seconds between polls. -/
  interval : Nat
  /-- When it stops being accepted. -/
  expires : Nat

/-- Record a new device authorization under the hash of its device code. -/
def Store.addDeviceCode (s : Store) (deviceCodeHash : SecretHash) (d : DeviceCode) :
    IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO device_codes (device_code_hash, user_code, client_id, scope, status, \
      interval, expires) VALUES (?, ?, ?, ?, 'pending', ?, ?)"
    #[deviceCodeHash, d.userCode, d.clientId, d.scope, d.interval, d.expires]

/-- The pending device authorization a user code names, for the approval page. -/
def Store.findPendingDeviceCode (s : Store) (userCode : String) (now : Nat) :
    IO (Option DeviceCode) := s.run fun c =>
  queryOne c
    "SELECT user_code, client_id, scope, interval, expires FROM device_codes \
      WHERE user_code = ? AND status = 'pending' AND expires > ?"
    #[userCode, now] fun st => do
      return { userCode := ← colText st 0, clientId := ← colText st 1,
               scope := ← colText st 2, interval := ← colNat st 3, expires := ← colNat st 4 }

/-- Approve or deny a pending device authorization by its user code.  Applies
only to one that is still pending and unexpired.  Whether it applied. -/
def Store.decideDeviceCode (s : Store) (userCode : String) (decision : DeviceStatus)
    (now : Nat) : IO Bool := s.run fun c => do
  let n ← match decision with
    | .approved user amr authTime =>
      exec c ("UPDATE device_codes SET status = 'approved', user_id = ?, amr = ?, " ++
          "auth_time = ? WHERE user_code = ? AND status = 'pending' AND expires > ?")
        #[user, encodeList amr, authTime, userCode, now]
    | .denied =>
      exec c ("UPDATE device_codes SET status = 'denied' " ++
          "WHERE user_code = ? AND status = 'pending' AND expires > ?")
        #[userCode, now]
    | .pending => pure 0
  return n > 0

/-- What a poll with a device code came to (RFC 8628 §3.5). -/
inductive DevicePoll where
  /-- Approved: the authorization is consumed and here is what to issue. -/
  | approved (clientId scope : String) (user : UserId) (amr : List String) (authTime : Nat)
  /-- Still waiting. -/
  | pending
  /-- Polled sooner than `interval` after the previous poll. -/
  | slowDown
  /-- The user refused; the authorization is consumed. -/
  | denied
  /-- No such code, or it has expired. -/
  | expired

/-- Remove expired device authorizations; how many. -/
def Store.purgeDeviceCodes (s : Store) (now : Nat) : IO Nat := s.run fun c =>
  exec c "DELETE FROM device_codes WHERE expires <= ?" #[now]

/-! ## Signing keys -/

/-- Where a signing key is in its rotation (§6.3). -/
inductive KeyState where
  /-- Published, not yet signing: services learn it before it is used. -/
  | next
  /-- Signing. -/
  | current
  /-- No longer signing, still published so tokens it signed verify. -/
  | previous
  /-- Neither signing nor published. -/
  | retired
  deriving BEq, Repr, Inhabited

/-- The name stored in the `state` column. -/
def KeyState.toString : KeyState → String
  | .next => "next"
  | .current => "current"
  | .previous => "previous"
  | .retired => "retired"

/-- Parse a `state` column. -/
def KeyState.ofString? : String → Option KeyState
  | "next" => some .next
  | "current" => some .current
  | "previous" => some .previous
  | "retired" => some .retired
  | _ => none

/-- A signing key as stored. -/
structure StoredKey where
  /-- The `kid` it is published under. -/
  kid : String
  /-- The JOSE algorithm name (`ES256`, `EdDSA`, `RS256`). -/
  algorithm : String
  /-- Where it is in its rotation. -/
  state : KeyState
  /-- The serialised private key, sealed under the root key with the `kid` as
  associated data. -/
  sealedKey : ByteArray
  /-- The public key, for the JWKS. -/
  publicKey : ByteArray
  /-- When it was generated. -/
  created : Nat

/-- Read a key row. -/
private def readKey (st : SQLite.Stmt) : IO StoredKey := do
  let stateName ← colText st 2
  let some state := KeyState.ofString? stateName
    | throw (.userError s!"store: unknown key state '{stateName}'")
  return { kid := ← colText st 0, algorithm := ← colText st 1, state,
           sealedKey := ← colBlob st 3, publicKey := ← colBlob st 4, created := ← colNat st 5 }

/-- Every key not retired, newest first. -/
def Store.listKeys (s : Store) : IO (Array StoredKey) := s.run fun c =>
  query c "SELECT kid, algorithm, state, sealed, public_key, created FROM keys \
    WHERE state != 'retired' ORDER BY created DESC, kid" #[] readKey

/-- Rotate: the current key becomes previous, the previous one retired, and
the given next key current, in one transaction.  Whether there was such a next
key. -/
def Store.promoteKey (s : Store) (kid : String) : IO Bool := s.atomically fun c => do
  let isNext ← queryOne c "SELECT 1 FROM keys WHERE kid = ? AND state = 'next'" #[kid]
    (colInt · 0)
  if isNext.isNone then return false
  discard <| exec c "UPDATE keys SET state = 'retired' WHERE state = 'previous'"
  discard <| exec c "UPDATE keys SET state = 'previous' WHERE state = 'current'"
  discard <| exec c "UPDATE keys SET state = 'current' WHERE kid = ?" #[kid]
  return true

/-! ## Invitations -/

/-- An invitation to create an account. -/
structure Invitation where
  /-- The account name it creates. -/
  userName : String
  /-- The groups the account gets. -/
  groups : List String
  /-- The administrator who issued it. -/
  createdBy : String
  /-- When it was issued. -/
  created : Nat
  /-- When it stops being accepted. -/
  expires : Nat
  /-- The email address the account gets, if any (migration 8). -/
  email : Option String := none
  /-- The display name the account gets, if any (migration 8). -/
  displayName : Option String := none

/-- The columns of `invitations` but its token hash, in the order
`readInvitation` reads them. -/
def invitationColumns : String :=
  "user_name, groups, created_by, created, expires, email, display_name"

/-- Read an invitation row selected with `invitationColumns`. -/
def readInvitation (st : SQLite.Stmt) : IO Invitation := do
  return { userName := ← colText st 0, groups := ← colList st 1, createdBy := ← colText st 2,
           created := ← colNat st 3, expires := ← colNat st 4,
           email := ← colOpt colText st 5, displayName := ← colOpt colText st 6 }

/-- Record an invitation under the hash of its token.  The email address and
display name are stored as they are given: `SignIn.createInvitation` checks
them first. -/
def Store.addInvitation (s : Store) (tokenHash : SecretHash) (i : Invitation) : IO Unit :=
  s.run fun c => do
    discard <| exec c
      "INSERT INTO invitations (token_hash, user_name, groups, created_by, created, expires, \
        email, display_name) VALUES (?, ?, ?, ?, ?, ?, ?, ?)"
      #[tokenHash, i.userName, encodeList i.groups, i.createdBy, i.created, i.expires,
        Value.opt i.email, Value.opt i.displayName]

/-- Consume an invitation: delete it and return it if it had not expired. -/
def Store.consumeInvitation (s : Store) (tokenHash : SecretHash) (now : Nat) :
    IO (Option Invitation) := s.run fun c => do
  let row ← queryOne c
    s!"DELETE FROM invitations WHERE token_hash = ? RETURNING {invitationColumns}"
    #[tokenHash] readInvitation
  return row.filter (now < ·.expires)

/-- The invitations not yet used and not expired at `now`, newest first, each
with the hash of its token: what the administration pages list and withdraw
them by.  The hash names an invitation without being one: only the token
opens `/invite/<token>`, and the token is never stored. -/
def Store.listInvitations (s : Store) (now : Nat) : IO (Array (SecretHash × Invitation)) :=
  s.run fun c => query c
    s!"SELECT token_hash, {invitationColumns} FROM invitations WHERE expires > ? \
      ORDER BY created DESC, user_name" #[now]
    fun st => do
      let h := SecretHash.ofStored (← colBlob st 0)
      let i : Invitation :=
        { userName := ← colText st 1, groups := ← colList st 2, createdBy := ← colText st 3,
          created := ← colNat st 4, expires := ← colNat st 5,
          email := ← colOpt colText st 6, displayName := ← colOpt colText st 7 }
      return (h, i)

/-- Withdraw an invitation by the hash of its token, used or expired or not:
the invitation as it was, if there was one. -/
def Store.revokeInvitation (s : Store) (tokenHash : SecretHash) : IO (Option Invitation) :=
  s.run fun c => queryOne c
    s!"DELETE FROM invitations WHERE token_hash = ? RETURNING {invitationColumns}"
    #[tokenHash] readInvitation

end Store
end Pyle