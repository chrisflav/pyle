import Lake
open Lake DSL

package pyle where
  version := v!"0.1.0"
  testDriver := "tests"
  -- OpenSSL's libcrypto, for signing, randomness, the AEAD, Argon2id and
  -- constant-time comparison (DESIGN.md §6).  The Lean toolchain ships it as a
  -- static library, so the binary needs nothing installed where it runs.
  moreLinkArgs := #["-lcrypto"]

-- Every dependency is pinned to a revision: the properties in DESIGN.md §9 are
-- stated over what these build, and a dependency that moved underneath them
-- would make the statements about something else.

-- The biscuit format and datalog, and the P-256 and Ed25519 verifiers.  On the
-- branch of chrisflav/lean-biscuit#1 until it merges.
require «lean-biscuit» from git
  "https://github.com/chrisflav/lean-biscuit" @ "669c5c8961eb10dbc6b61e6567b3c4c0b01004bb"

-- SHA-1, SHA-2 and HMAC.
require «lean-crypto-hash» from git
  "https://github.com/kim-em/lean-crypto-hash" @ "4fa361c69f257a05c3203b065bbc65ef1cd63b03"

-- SQLite, with the amalgamation built in.
require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "0be4df908d1a8e75b58961041e2b4973692623df"

/-- Compile a C shim under `ffi/` into a static library of the same name. -/
private def ffiStaticLib (pkg : Package) (name : String) : FetchM (Job System.FilePath) := do
  let cFile := pkg.dir / "ffi" / s!"{name}.c"
  let cSrc ← inputTextFile cFile
  let oFile := pkg.buildDir / "ffi" / s!"{name}.o"
  let oJob ← buildFileAfterDep oFile cSrc fun _ => do
    compileO oFile cFile #["-I", (← getLeanIncludeDir).toString, "-fPIC", "-O2", "-Wall"]
  let libFile := pkg.buildDir / "lib" / nameToStaticLib name
  liftM <| buildFileAfterDep libFile oJob fun oFile => do
    compileStaticLib libFile #[oFile]

/-- Everything that touches a secret: randomness, signing, the AEAD, Argon2id
and constant-time comparison, backing `Pyle.Crypto.Ffi`. -/
extern_lib PyleFfi pkg := ffiStaticLib pkg "PyleFfi"

/-- The POSIX calls behind `Pyle.Sys`: creating the root key with `O_EXCL` and
mode 0600, and `umask`. -/
extern_lib PyleSys pkg := ffiStaticLib pkg "PyleSys"

@[default_target]
lean_lib Pyle

lean_lib PyleTests where
  globs := #[.submodules `PyleTests]

/-- The server and its administration commands. -/
@[default_target]
lean_exe pyle where
  root := `Main

lean_exe tests where
  root := `PyleTests.Main