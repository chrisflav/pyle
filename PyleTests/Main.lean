import PyleTests.Crypto

/-!
# The test driver

Run as a compiled binary rather than through `lean --run`, because the tests
call into the FFI shim and the interpreter cannot resolve statically linked
symbols.
-/

open PyleTests

def main : IO UInt32 := do
  cryptoTests
  report