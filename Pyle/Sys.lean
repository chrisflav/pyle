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
installed (and the old bytes overwritten, when `old` is not empty); `1` if
`newPath` did not exist; `2` if installed without overwriting the old bytes
(the file was not writable, a 0400 one say, or did not hold them).
Overwriting is best effort even then: a copy-on-write filesystem or an SSD
may keep the old blocks.  Call it holding the root key's lock (`withLock`). -/
@[extern "pyle_sys_install_file"]
opaque installFile (newPath path : @& String) (old : @& ByteArray) : IO UInt8

/-- Take an exclusive `flock` on `path` (created with mode 0600 if need be,
never through a symbolic link): the descriptor that holds it, or — when
`wait` is false and another descriptor holds it — `UInt32.max` at once.  Two
descriptors exclude each other even within one process. -/
@[extern "pyle_sys_lock"]
opaque lockRaw (path : @& String) (wait : Bool) : IO UInt32

/-- Release a lock `lockRaw` took. -/
@[extern "pyle_sys_unlock"]
opaque unlock (fd : UInt32) : IO Unit

/-- Run `act` holding the exclusive lock on `path`, waiting for it if `wait`;
`none` without running it if `wait` is false and the lock is taken. -/
def withLock (path : String) (wait : Bool) (act : IO α) : IO (Option α) := do
  let fd ← lockRaw path wait
  if fd == UInt32.ofNat 4294967295 then return none
  try return some (← act) finally unlock fd

end Sys
end Pyle