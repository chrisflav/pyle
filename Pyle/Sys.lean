/-!
# Operating-system calls

The declarations backed by `ffi/PyleSys.c`: creating a private file without a
window in which it is readable by others, the process's `umask`, and
replacing a file durably, for `pyle root-key rotate`.  See the C file for why
`IO.FS` is not enough here.
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

/-- `fsync` a directory, so that the entries created or renamed in it survive
a power failure. -/
@[extern "pyle_sys_fsync_dir"]
opaque fsyncDir (path : @& String) : IO Unit

/-- Rename `newPath` over `path` and `fsync` the directory holding `path`.  If
`path` held exactly `old` before, those bytes are overwritten with zeros
afterwards, through a descriptor opened before the rename, so that a file
another process installed in the meantime is never touched.  `0` once
installed; `1` if `newPath` did not exist, because another process installed
it first. -/
@[extern "pyle_sys_install_file"]
opaque installFile (newPath path : @& String) (old : @& ByteArray) : IO UInt8

end Sys
end Pyle