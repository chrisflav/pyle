/-!
# Operating-system calls

The declarations backed by `ffi/PyleSys.c`: creating a private file without a
window in which it is readable by others, and the process's `umask`.  See the
C file for why `IO.FS` is not enough here.
-/

namespace Pyle
namespace Sys

/-- Set the process's file-mode creation mask, returning the previous one. -/
@[extern "pyle_sys_umask"]
opaque umask (mask : UInt32) : IO UInt32

/-- Create `path` with mode 0600 and write `data` to it.  Fails if `path`
exists, including as a symbolic link. -/
@[extern "pyle_sys_write_new_private"]
opaque writeNewPrivate (path : @& String) (data : @& ByteArray) : IO Unit

end Sys
end Pyle