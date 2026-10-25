import PyleTests.Crypto
import PyleTests.Store
import PyleTests.Http
import PyleTests.Session
import PyleTests.Audit
import PyleTests.Factor
import PyleTests.WebAuthn
import PyleTests.SignIn
import PyleTests.Account
import PyleTests.Web

/-!
# The test driver

Run as a compiled binary rather than through `lean --run`, because the tests
call into the FFI shim and the interpreter cannot resolve statically linked
symbols.
-/

open PyleTests

def main : IO UInt32 := do
  cryptoTests
  storeTests
  httpTests
  sessionTests
  auditTests
  factorTests
  webAuthnTests
  signInTests
  accountTests
  webTests
  report