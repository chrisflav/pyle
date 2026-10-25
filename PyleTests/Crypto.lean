import PyleTests.Harness

/-!
# The constant-time boundary

The FFI shim, exercised through its Lean declarations.
-/

namespace PyleTests

open Pyle

def cryptoTests : IO Unit := do
  group "crypto: ffi"
  let a ← Crypto.randomBytes 32
  let b ← Crypto.randomBytes 32
  checkEq "random bytes have the requested length" a.size 32
  check "two draws differ" (a != b)
  check "ctEqual: equal" (Crypto.ctEqual a (a.extract 0 32))
  check "ctEqual: different" (!Crypto.ctEqual a b)
  check "ctEqual: different lengths" (!Crypto.ctEqual a (a.extract 0 31))
  checkEq "zero bytes" (← Crypto.randomBytes 0).size 0

end PyleTests