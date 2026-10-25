/*
 * The few POSIX calls pyle needs that Lean's standard library does not offer.
 *
 * Creating the root key safely needs `open` with `O_CREAT | O_EXCL |
 * O_NOFOLLOW` and mode 0600: the file must not exist beforehand (so nothing
 * is replaced, and nobody can have opened it already), must not be reached
 * through a symbolic link someone planted, and must never be readable by
 * anyone else, not even for a moment.  Lean's `IO.FS` creates files with the
 * process's default mode and changes it afterwards, which leaves a window.
 *
 * `umask` is here so that the database and its journal files, which SQLite
 * creates itself, are created private too.
 *
 * Every function either returns its result or raises an IO error; none of
 * them abort the process.
 */

#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

/* Set the process's file-mode creation mask; returns the previous one. */
LEAN_EXPORT lean_obj_res pyle_sys_umask(uint32_t mask, lean_obj_arg w) {
    (void)w;
    mode_t old = umask((mode_t)mask);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)old));
}

/* Create `path`, which must not exist and must not be a symbolic link, with
 * mode 0600, and write `data` to it through the same descriptor. */
LEAN_EXPORT lean_obj_res pyle_sys_write_new_private(b_lean_obj_arg path, b_lean_obj_arg data,
                                                    lean_obj_arg w) {
    (void)w;
    const char *p = lean_string_cstr(path);
    int fd = open(p, O_CREAT | O_EXCL | O_NOFOLLOW | O_WRONLY | O_CLOEXEC, 0600);
    if (fd < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, path));
    const uint8_t *buf = lean_sarray_cptr(data);
    size_t left = lean_sarray_size(data);
    while (left > 0) {
        ssize_t n = write(fd, buf, left);
        if (n < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            close(fd);
            unlink(p);
            return lean_io_result_mk_error(lean_decode_io_error(e, path));
        }
        buf += n;
        left -= (size_t)n;
    }
    if (fsync(fd) != 0 || close(fd) != 0) {
        int e = errno;
        unlink(p);
        return lean_io_result_mk_error(lean_decode_io_error(e, path));
    }
    return lean_io_result_mk_ok(lean_box(0));
}