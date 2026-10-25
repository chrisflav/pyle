/-!
# The constant-time boundary

The declarations backed by `ffi/PyleFfi.c`.  Anything that generates, signs
with or compares a secret goes through here; see DESIGN.md §6.2 for why this is
not written in Lean.
-/

namespace Pyle
namespace Crypto

/-- `n` bytes from the operating system's random generator. -/
@[extern "pyle_random_bytes"]
opaque randomBytes (n : USize) : IO ByteArray

/-- Equality of two byte strings, in time that depends only on their lengths. -/
@[extern "pyle_ct_equal"]
opaque ctEqual (a b : @& ByteArray) : Bool

end Crypto
end Pyle