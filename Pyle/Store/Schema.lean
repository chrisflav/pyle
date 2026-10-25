import Pyle.Store.Db

/-!
# The schema and its migrations

The tables of DESIGN.md §8, plus `invitations` (accounts are created by an
administrator or by invitation, never by sign-up) and `device_codes` (the
device authorization grant of §5.5).

A migration is a numbered list of statements.  `schema_version` records which
numbers have been applied, and `migrate` applies the missing ones in order,
each in its own transaction together with the row that records it, so a crash
leaves the database at one version or the next and never in between.
Migrations are only ever appended: a database written by an older pyle is
brought forward, and one written by a newer pyle than this is refused rather
than misread.

Times are integer seconds since the Unix epoch.  Every table that holds a
bearer secret holds its SHA-256 (`Store.SecretHash`), never the secret.
-/

namespace Pyle
namespace Store

/-- One step of the schema's history. -/
structure Migration where
  /-- Its number; migrations are applied in increasing order. -/
  version : Nat
  /-- What it is for, recorded alongside the version. -/
  description : String
  /-- The statements it runs.  None of them take parameters. -/
  statements : List String

/-- The first schema: everything DESIGN.md §8 lists. -/
def migration1 : Migration where
  version := 1
  description := "initial schema"
  statements := [
    -- `handle` is the WebAuthn user handle: random, so it says nothing about
    -- the account.  `name` is what people and services see.
    "CREATE TABLE users (
       id INTEGER PRIMARY KEY,
       handle BLOB NOT NULL UNIQUE,
       name TEXT NOT NULL UNIQUE,
       groups TEXT NOT NULL DEFAULT '[]',
       created INTEGER NOT NULL,
       disabled INTEGER NOT NULL DEFAULT 0
     ) STRICT",
    "CREATE TABLE webauthn_credentials (
       id BLOB PRIMARY KEY,
       user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
       algorithm INTEGER NOT NULL,
       public_key BLOB NOT NULL,
       sign_count INTEGER NOT NULL,
       backup_eligible INTEGER NOT NULL,
       backup_state INTEGER NOT NULL,
       aaguid BLOB NOT NULL,
       transports TEXT NOT NULL DEFAULT '[]',
       name TEXT NOT NULL,
       created INTEGER NOT NULL,
       last_used INTEGER
     ) STRICT",
    "CREATE INDEX webauthn_credentials_user ON webauthn_credentials(user_id)",
    -- `secret` is sealed under the root key with the user id as associated
    -- data (§6.3).  `failures` and `locked_until` are the TOTP lock of §7.
    "CREATE TABLE totp (
       user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
       secret BLOB NOT NULL,
       last_step INTEGER,
       failures INTEGER NOT NULL DEFAULT 0,
       locked_until INTEGER NOT NULL DEFAULT 0,
       created INTEGER NOT NULL
     ) STRICT",
    "CREATE TABLE recovery_codes (
       user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
       digest BLOB NOT NULL,
       spent_at INTEGER,
       PRIMARY KEY (user_id, digest)
     ) STRICT",
    "CREATE TABLE sessions (
       id_hash BLOB PRIMARY KEY,
       user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
       amr TEXT NOT NULL,
       factors TEXT NOT NULL,
       auth_time INTEGER NOT NULL,
       created INTEGER NOT NULL,
       last_seen INTEGER NOT NULL,
       client_address TEXT NOT NULL,
       user_agent TEXT NOT NULL
     ) STRICT",
    "CREATE INDEX sessions_user ON sessions(user_id)",
    "CREATE TABLE challenges (
       challenge BLOB PRIMARY KEY,
       purpose TEXT NOT NULL,
       user_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
       expires INTEGER NOT NULL
     ) STRICT",
    "CREATE TABLE clients (
       id TEXT PRIMARY KEY,
       name TEXT NOT NULL,
       secret_hash BLOB,
       redirect_uris TEXT NOT NULL,
       scopes TEXT NOT NULL,
       created INTEGER NOT NULL
     ) STRICT",
    -- Every field an authorization code is bound to (§5.1).
    "CREATE TABLE codes (
       code_hash BLOB PRIMARY KEY,
       client_id TEXT NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
       redirect_uri TEXT NOT NULL,
       code_challenge TEXT NOT NULL,
       user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
       scope TEXT NOT NULL,
       nonce TEXT,
       amr TEXT NOT NULL,
       auth_time INTEGER NOT NULL,
       expires INTEGER NOT NULL
     ) STRICT",
    -- A refresh token belongs to a family; using a token marks it used and
    -- issues the next one in the same family, and presenting a used one
    -- revokes the family.
    "CREATE TABLE refresh_tokens (
       token_hash BLOB PRIMARY KEY,
       family BLOB NOT NULL,
       client_id TEXT NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
       user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
       scope TEXT NOT NULL,
       amr TEXT NOT NULL,
       auth_time INTEGER NOT NULL,
       created INTEGER NOT NULL,
       expires INTEGER NOT NULL,
       used_at INTEGER
     ) STRICT",
    "CREATE INDEX refresh_tokens_family ON refresh_tokens(family)",
    -- A family, once revoked, stays revoked: the trigger refuses any token
    -- added to it, whichever code path tries.
    "CREATE TABLE revoked_families (
       family BLOB PRIMARY KEY,
       revoked INTEGER NOT NULL
     ) STRICT",
    "CREATE TRIGGER refresh_tokens_not_revoked BEFORE INSERT ON refresh_tokens
       WHEN EXISTS (SELECT 1 FROM revoked_families WHERE family = NEW.family)
       BEGIN SELECT RAISE(ABORT, 'refresh-token family revoked'); END",
    "CREATE TABLE keys (
       kid TEXT PRIMARY KEY,
       algorithm TEXT NOT NULL,
       state TEXT NOT NULL CHECK (state IN ('next', 'current', 'previous', 'retired')),
       sealed BLOB NOT NULL,
       public_key BLOB NOT NULL,
       created INTEGER NOT NULL
     ) STRICT",
    -- The chain of §7: `hash` is SHA-256 over `prev` and the record.
    "CREATE TABLE audit (
       seq INTEGER PRIMARY KEY,
       time INTEGER NOT NULL,
       event TEXT NOT NULL,
       user_name TEXT,
       factor TEXT,
       client_address TEXT NOT NULL,
       outcome TEXT NOT NULL,
       detail TEXT NOT NULL,
       prev BLOB NOT NULL,
       hash BLOB NOT NULL
     ) STRICT",
    "CREATE TABLE invitations (
       token_hash BLOB PRIMARY KEY,
       user_name TEXT NOT NULL,
       groups TEXT NOT NULL,
       created_by TEXT NOT NULL,
       created INTEGER NOT NULL,
       expires INTEGER NOT NULL
     ) STRICT",
    -- RFC 8628: the device code is the CLI's secret, the user code what the
    -- person types.  `status` moves pending → approved | denied, and an
    -- approved row is deleted by the poll that collects it.
    "CREATE TABLE device_codes (
       device_code_hash BLOB PRIMARY KEY,
       user_code TEXT NOT NULL UNIQUE,
       client_id TEXT NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
       scope TEXT NOT NULL,
       status TEXT NOT NULL CHECK (status IN ('pending', 'approved', 'denied')),
       user_id INTEGER REFERENCES users(id) ON DELETE CASCADE,
       amr TEXT NOT NULL DEFAULT '[]',
       auth_time INTEGER,
       interval INTEGER NOT NULL,
       last_poll INTEGER NOT NULL DEFAULT 0,
       expires INTEGER NOT NULL
     ) STRICT"
  ]

/-- Passwords, for deployments that allow them (DESIGN §1, §3).  One per
user, as the PHC string of its Argon2id hash; the table is empty unless
`allowPasswords` is set. -/
def migration2 : Migration where
  version := 2
  description := "passwords"
  statements := [
    "CREATE TABLE passwords (
       user_id INTEGER PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
       phc TEXT NOT NULL,
       created INTEGER NOT NULL
     ) STRICT"
  ]

/-- Every migration, in order.  Append only. -/
def migrations : List Migration := [migration1, migration2]

/-- The version a fully migrated database is at. -/
def schemaVersion : Nat := (migrations.map (·.version)).foldl max 0

/-- The version a database is at: the largest recorded in `schema_version`,
or zero for a database that has none. -/
def currentVersion (c : SQLite) : IO Nat := do
  discard <| exec c "CREATE TABLE IF NOT EXISTS schema_version (
      version INTEGER PRIMARY KEY,
      description TEXT NOT NULL,
      applied INTEGER NOT NULL
    ) STRICT"
  let v ← queryOne c "SELECT COALESCE(MAX(version), 0) FROM schema_version" #[]
    (colNat · 0)
  return v.getD 0

/-- Bring the database up to `schemaVersion`.  Refuses a database from a newer
pyle.  Each migration reads the version and applies itself inside one
`BEGIN IMMEDIATE` transaction, so two processes starting on the same file
cannot both apply it: the second waits for the write lock and then sees the
version the first recorded. -/
def Store.migrate (s : Store) (now : Nat) : IO Unit := s.run fun c => do
  for m in migrations do
    c.transaction (mode := .immediate) do
      let atVersion ← currentVersion c
      if atVersion > schemaVersion then
        throw (.userError s!"the database is at schema version {atVersion}, newer than this \
          pyle understands ({schemaVersion}); refusing to touch it")
      if m.version > atVersion then
        for stmt in m.statements do
          discard <| exec c stmt
        discard <| exec c
          "INSERT INTO schema_version (version, description, applied) VALUES (?, ?, ?)"
          #[m.version, m.description, now]

/-- Open a database and migrate it. -/
def Store.openAt (path : System.FilePath) (now : Nat) : IO Store := do
  let s ← Store.openFile path
  s.migrate now
  return s

/-- The schema version of an open database. -/
def Store.version (s : Store) : IO Nat := s.run currentVersion

end Store
end Pyle