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
 * Replacing the root key (`pyle root-key rotate`) needs the replacement to be
 * durable before the database starts relying on it and after: `fsync` on the
 * directory holding it, and a `rename` over the old file followed by another
 * directory `fsync`.  The old key's bytes are overwritten through a descriptor
 * opened before the rename, and only if that file still held them then, so a
 * key that another process installed in the meantime is never touched.
 *
 * Every function either returns its result or raises an IO error; none of
 * them abort the process.
 */

#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/file.h>
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
    int synced = fsync(fd);
    int e = errno;
    int closed = close(fd);
    if (closed != 0 && synced == 0) e = errno;
    if (synced != 0 || closed != 0) {
        unlink(p);
        return lean_io_result_mk_error(lean_decode_io_error(e, path));
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Take an exclusive `flock` on `path`, creating it (mode 0600, not through a
 * symbolic link) if need be.  Blocks until it is free when `wait` is set;
 * otherwise returns UINT32_MAX at once if another descriptor holds it.
 * Returns the descriptor, which holds the lock until `pyle_sys_unlock`
 * closes it, or the process ends.  Locks taken through two descriptors
 * exclude each other even within one process. */
LEAN_EXPORT lean_obj_res pyle_sys_lock(b_lean_obj_arg path, uint8_t wait, lean_obj_arg w) {
    (void)w;
    int fd = open(lean_string_cstr(path), O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (fd < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, path));
    for (;;) {
        if (flock(fd, LOCK_EX | (wait ? 0 : LOCK_NB)) == 0)
            return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
        if (errno == EINTR) continue;
        int e = errno;
        close(fd);
        if (e == EWOULDBLOCK) return lean_io_result_mk_ok(lean_box_uint32(UINT32_MAX));
        return lean_io_result_mk_error(lean_decode_io_error(e, path));
    }
}

/* Release a lock taken by `pyle_sys_lock`. */
LEAN_EXPORT lean_obj_res pyle_sys_unlock(uint32_t fd, lean_obj_arg w) {
    (void)w;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Open a directory and fsync it, so that the entries created or renamed in it
 * survive a power failure. */
static int fsync_dir(const char *dir) {
    int fd = open(dir, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) return -1;
    int r = fsync(fd);
    int e = errno;
    close(fd);
    errno = e;
    return r;
}

/* The directory part of a path: everything before the last '/', "/" for a
 * file in the root, "." for a bare name.  Allocated with malloc. */
static char *dir_of(const char *p) {
    const char *slash = strrchr(p, '/');
    if (slash == NULL) return strdup(".");
    if (slash == p) return strdup("/");
    size_t n = (size_t)(slash - p);
    char *d = malloc(n + 1);
    if (d == NULL) return NULL;
    memcpy(d, p, n);
    d[n] = 0;
    return d;
}

/* fsync the directory `path`. */
LEAN_EXPORT lean_obj_res pyle_sys_fsync_dir(b_lean_obj_arg path, lean_obj_arg w) {
    (void)w;
    if (fsync_dir(lean_string_cstr(path)) != 0)
        return lean_io_result_mk_error(lean_decode_io_error(errno, path));
    return lean_io_result_mk_ok(lean_box(0));
}

/* The largest file `pyle_sys_install_file` compares and overwrites. */
#define INSTALL_MAX 4096

/* Install `new_path` as `path`: rename it over `path` and fsync the directory.
 * If `path` held exactly `old` just before, those bytes are then overwritten
 * with zeros, through a descriptor opened before the rename, and synced.
 * Returns 0 once installed (and the old bytes overwritten, if `old` was given),
 * 1 if `new_path` did not exist, 2 if installed but the old bytes were not
 * overwritten.  Overwriting is best effort in any case: a copy-on-write
 * filesystem or an SSD may keep the old blocks.  Callers hold the root key's
 * lock (`pyle_sys_lock`), so nothing else renames into `path` meanwhile. */
LEAN_EXPORT lean_obj_res pyle_sys_install_file(b_lean_obj_arg new_path, b_lean_obj_arg path,
                                               b_lean_obj_arg old, lean_obj_arg w) {
    (void)w;
    const char *np = lean_string_cstr(new_path);
    const char *p = lean_string_cstr(path);
    size_t old_size = lean_sarray_size(old);
    int scrub = 0;
    int fd = open(p, O_RDWR | O_NOFOLLOW | O_CLOEXEC);
    if (fd >= 0 && old_size > 0 && old_size <= INSTALL_MAX) {
        uint8_t buf[INSTALL_MAX + 1];
        size_t got = 0;
        while (got < sizeof buf) {
            ssize_t n = pread(fd, buf + got, sizeof buf - got, (off_t)got);
            if (n < 0 && errno == EINTR) continue;
            if (n <= 0) break;
            got += (size_t)n;
        }
        scrub = got == old_size && memcmp(buf, lean_sarray_cptr(old), old_size) == 0;
        memset(buf, 0, sizeof buf);
    }
    if (rename(np, p) != 0) {
        int e = errno;
        if (fd >= 0) close(fd);
        if (e == ENOENT) return lean_io_result_mk_ok(lean_box(1));
        return lean_io_result_mk_error(lean_decode_io_error(e, new_path));
    }
    char *dir = dir_of(p);
    int r = dir == NULL ? -1 : fsync_dir(dir);
    int e = dir == NULL ? ENOMEM : errno;
    free(dir);
    if (r != 0) {
        if (fd >= 0) close(fd);
        return lean_io_result_mk_error(lean_decode_io_error(e, path));
    }
    int scrubbed = 0;
    if (scrub) {
        uint8_t zeros[INSTALL_MAX];
        memset(zeros, 0, sizeof zeros);
        size_t done = 0;
        while (done < old_size) {
            ssize_t n = pwrite(fd, zeros, old_size - done, (off_t)done);
            if (n < 0 && errno == EINTR) continue;
            if (n <= 0) break;
            done += (size_t)n;
        }
        scrubbed = done == old_size && fsync(fd) == 0;
    }
    if (fd >= 0) close(fd);
    /* 2: installed, but the old bytes were not overwritten (the file could
     * not be opened for writing, say a 0400 file, or did not hold them). */
    return lean_io_result_mk_ok(lean_box(scrubbed || old_size == 0 ? 0 : 2));
}