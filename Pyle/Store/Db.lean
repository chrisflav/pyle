import SQLite
import LeanBiscuit.Crypto.Hash
import Std.Sync.Mutex

/-!
# The database connection

pyle keeps all of its state in one SQLite file (DESIGN.md §8).  This module is
the only place that talks to `leansqlite` directly, and it does so in one way:
a statement is a fixed SQL string and a list of `Value`s bound to its `?`
parameters.  There is no function here that splices a value into SQL text, so
there is nothing for a caller to get wrong about quoting.

One connection serves the whole process, behind a mutex.  The HTTP server runs
handlers concurrently, and SQLite transactions belong to a connection rather
than to a thread: two handlers interleaving `BEGIN … COMMIT` on one connection
would each commit the other's half.  Every public store function therefore
takes the lock once, for the whole of what it does, and the helpers below that
it calls take the bare connection.

Secrets that work as bearer credentials — session identifiers, authorization
codes, refresh tokens, device codes, invitation tokens — are never stored as
they are.  The store's functions take a `SecretHash`, which is the SHA-256 of
the secret, so reading the database does not hand anyone a working credential.
-/

namespace Pyle
namespace Store

/-- A value bound to a statement parameter. -/
inductive Value where
  /-- SQL `NULL`. -/
  | null
  /-- A 64-bit integer.  Values outside the range of `Int64` wrap, so callers
  only bind times, counters and row ids, which stay far below it. -/
  | int (n : Int)
  /-- UTF-8 text. -/
  | text (s : String)
  /-- Bytes. -/
  | blob (b : ByteArray)
  deriving Inhabited

instance : Coe String Value := ⟨.text⟩
instance : Coe ByteArray Value := ⟨.blob⟩
instance : Coe Int Value := ⟨.int⟩
instance : Coe Nat Value := ⟨fun n => .int n⟩

/-- An optional value, as `NULL` when it is absent. -/
def Value.opt {α : Type} [Coe α Value] : Option α → Value
  | none => .null
  | some a => (a : Value)

/-- Bind a value to the 1-based parameter `i` of a statement. -/
def Value.bindTo (stmt : SQLite.Stmt) (i : Int32) : Value → IO Unit
  | .null => stmt.bindNull i
  | .int n => stmt.bindInt64 i (Int64.ofInt n)
  | .text s => stmt.bindText i s
  | .blob b => stmt.bindBlob i b

/-- The SHA-256 of a bearer secret: what the database stores in its place.
Only `SecretHash.of` makes one, so a value of this type is never the secret
itself. -/
structure SecretHash where private mk ::
  /-- The 32-byte digest. -/
  bytes : ByteArray

/-- Hash a secret for storage or lookup. -/
def SecretHash.of (secret : ByteArray) : SecretHash :=
  ⟨LeanBiscuit.Sha256.hash secret⟩

/-- Read a stored digest back.  The bytes came out of the database, where only
`SecretHash.of` could have put them. -/
def SecretHash.ofStored (digest : ByteArray) : SecretHash := ⟨digest⟩

instance : Coe SecretHash Value := ⟨fun h => .blob h.bytes⟩

instance : BEq SecretHash := ⟨fun a b => a.bytes == b.bytes⟩

/-- The open database, with the lock that serialises access to it. -/
structure Store where
  /-- The connection. -/
  conn : SQLite
  /-- Held for the whole of every public store operation; see the module
  documentation for why. -/
  lock : Std.Mutex Unit

/-- Run an operation on the connection, holding the lock. -/
def Store.run (s : Store) (act : SQLite → IO α) : IO α :=
  s.lock.atomically (m := IO) (fun _ => act s.conn)

/-- Run an operation inside one `BEGIN IMMEDIATE` transaction, holding the
lock.  `IMMEDIATE` takes the write lock at the start, so a read followed by a
write inside it cannot race another process writing the same file. -/
def Store.atomically (s : Store) (act : SQLite → IO α) : IO α :=
  s.run fun c => c.transaction (act c) (mode := .immediate)

/-! ## Statements -/

/-- Prepare a statement and bind its parameters in order. -/
def prepareWith (c : SQLite) (sql : String) (params : Array Value) : IO SQLite.Stmt := do
  let stmt ← c.prepare sql
  for h : i in [0:params.size] do
    params[i].bindTo stmt (Int32.ofNat (i + 1))
  return stmt

/-- Run a statement that returns no rows; the number of rows it changed. -/
def exec (c : SQLite) (sql : String) (params : Array Value := #[]) : IO Nat := do
  let stmt ← prepareWith c sql params
  while ← stmt.step do pure ()
  stmt.reset
  return (← c.changes).toInt.toNat

/-- Run a statement and read every row it returns. -/
def query (c : SQLite) (sql : String) (params : Array Value)
    (read : SQLite.Stmt → IO α) : IO (Array α) := do
  let stmt ← prepareWith c sql params
  let mut rows := #[]
  while ← stmt.step do
    rows := rows.push (← read stmt)
  stmt.reset
  return rows

/-- Run a statement and read its first row, if it returns one.  The statement
is run to completion either way, so a `DELETE … RETURNING` deletes everything
it matches. -/
def queryOne (c : SQLite) (sql : String) (params : Array Value)
    (read : SQLite.Stmt → IO α) : IO (Option α) :=
  return (← query c sql params read)[0]?

/-! ## Columns

Columns are read by their 0-based position in the `SELECT` or `RETURNING`
list.  The readers fail rather than guess when a column holds `NULL` where a
value is required: that is a database that does not match the schema. -/

/-- Whether a column is `NULL`. -/
def isNull (stmt : SQLite.Stmt) (i : Nat) : IO Bool :=
  stmt.columnNull (Int32.ofNat i)

/-- An integer column. -/
def colInt (stmt : SQLite.Stmt) (i : Nat) : IO Int := do
  if ← isNull stmt i then throw (.userError s!"store: column {i} is unexpectedly NULL")
  return (← stmt.columnInt64 (Int32.ofNat i)).toInt

/-- A non-negative integer column, such as a time or a counter. -/
def colNat (stmt : SQLite.Stmt) (i : Nat) : IO Nat :=
  return (← colInt stmt i).toNat

/-- A text column. -/
def colText (stmt : SQLite.Stmt) (i : Nat) : IO String := do
  if ← isNull stmt i then throw (.userError s!"store: column {i} is unexpectedly NULL")
  stmt.columnText (Int32.ofNat i)

/-- A blob column. -/
def colBlob (stmt : SQLite.Stmt) (i : Nat) : IO ByteArray := do
  if ← isNull stmt i then throw (.userError s!"store: column {i} is unexpectedly NULL")
  stmt.columnBlob (Int32.ofNat i)

/-- A nullable column, read with `read` when it is not `NULL`. -/
def colOpt (read : SQLite.Stmt → Nat → IO α) (stmt : SQLite.Stmt) (i : Nat) :
    IO (Option α) := do
  if ← isNull stmt i then return none
  return some (← read stmt i)

/-! ## Lists in a column

A few columns hold short lists of names (`amr` values, groups, redirect URIs).
They are stored as a JSON array of strings, which SQLite can read with its own
JSON functions if an administrator needs to query them. -/

/-- Encode a list of strings for a column. -/
def encodeList (xs : List String) : String :=
  (Lean.Json.arr (xs.map Lean.Json.str).toArray).compress

/-- Decode a list of strings from a column; anything that is not a JSON array
of strings is an error. -/
def decodeList (s : String) : Except String (List String) := do
  let j ← Lean.Json.parse s
  let arr ← j.getArr?
  arr.toList.mapM fun v => v.getStr?

/-- A list column. -/
def colList (stmt : SQLite.Stmt) (i : Nat) : IO (List String) := do
  match decodeList (← colText stmt i) with
  | .ok xs => return xs
  | .error e => throw (.userError s!"store: column {i} is not a list of strings: {e}")

/-! ## Opening -/

/-- Open (creating if needed) the database file.  Foreign keys are switched on,
since SQLite leaves them off by default, and the journal is put in WAL mode so
that readers do not block the writer. -/
def Store.openFile (path : System.FilePath) : IO Store := do
  let conn ← SQLite.openWith path .readWriteCreate (busyTimeoutMs := 5000)
  conn.exec "PRAGMA foreign_keys = ON"
  conn.exec "PRAGMA journal_mode = WAL"
  conn.exec "PRAGMA synchronous = NORMAL"
  return { conn, lock := ← Std.Mutex.new () }

end Store
end Pyle