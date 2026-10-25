/*
 * Everything in pyle that touches a secret.
 *
 * The Lean code is the specification: it verifies signatures, parses and
 * decides.  Whatever handles a secret value -- generating it, signing with it,
 * comparing it -- runs here, against a library that promises constant time,
 * because Lean promises nothing about the timing of compiled code (DESIGN.md
 * §6.2).
 *
 * Every function either returns its result or raises an IO error with a
 * message; none of them abort the process.
 */

#include <lean/lean.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/rand.h>
#include <stdio.h>

/* An IO error carrying the most recent OpenSSL error, prefixed with `what`. */
static lean_obj_res pyle_openssl_error(const char *what) {
    char buf[512];
    unsigned long e = ERR_get_error();
    snprintf(buf, sizeof(buf), "%s: %s", what, e ? ERR_error_string(e, NULL) : "unknown error");
    ERR_clear_error();
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

/* `n` bytes from the operating system's generator, through OpenSSL's DRBG. */
LEAN_EXPORT lean_obj_res pyle_random_bytes(size_t n, lean_obj_arg w) {
    (void)w;
    lean_object *arr = lean_alloc_sarray(1, n, n);
    if (n > 0 && RAND_bytes(lean_sarray_cptr(arr), (int)n) != 1) {
        lean_dec(arr);
        return pyle_openssl_error("RAND_bytes");
    }
    return lean_io_result_mk_ok(arr);
}

/* Equality of two byte strings in time that depends only on their lengths.
 * The lengths themselves are not secret: every value compared this way has a
 * length fixed by its format. */
LEAN_EXPORT uint8_t pyle_ct_equal(b_lean_obj_arg a, b_lean_obj_arg b) {
    size_t n = lean_sarray_size(a);
    if (n != lean_sarray_size(b)) return 0;
    return CRYPTO_memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), n) == 0;
}