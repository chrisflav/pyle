/*
 * Everything in pyle that touches a secret.
 *
 * The Lean code is the specification: it verifies signatures, parses and
 * decides.  Whatever handles a secret value -- generating it, signing with it,
 * encrypting under it, deriving from it, comparing it -- runs here, against a
 * library that promises constant time, because Lean promises nothing about the
 * timing of compiled code (DESIGN.md §6.2).
 *
 * The library is the static libcrypto the Lean toolchain ships (3.6 at the
 * time of writing), while the headers come from whatever libssl-dev the build
 * machine has, which may be as old as 3.0.  So this file uses only interfaces
 * that 3.0 already has.  Argon2id arrived in 3.2; it is fetched by name at run
 * time, which needs no newer header, and a library without it is reported as
 * an error rather than discovered as a missing symbol at link time.
 *
 * Every function either returns its result or raises an IO error (or returns
 * `Except.error`) with a message; none of them abort the process.  Wherever a
 * secret is copied into memory this file owns, the copy is wiped with
 * OPENSSL_cleanse before it is released.
 */

#include <lean/lean.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>

#include <openssl/core_names.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/kdf.h>
#include <openssl/params.h>
#include <openssl/rand.h>
#include <openssl/x509.h>
#include <openssl/x509_vfy.h>

/* ------------------------------------------------------------------ */
/* Results                                                              */
/* ------------------------------------------------------------------ */

/* `msg`, followed by the most recent OpenSSL error if there is one, into
 * `buf`; the OpenSSL error queue is cleared either way. */
static void pyle_describe(char *buf, size_t size, const char *msg) {
    unsigned long e = ERR_get_error();
    if (e) {
        char detail[256];
        ERR_error_string_n(e, detail, sizeof(detail));
        snprintf(buf, size, "%s: %s", msg, detail);
    } else {
        snprintf(buf, size, "%s", msg);
    }
    ERR_clear_error();
}

/* An IO error carrying `what` and the most recent OpenSSL error. */
static lean_obj_res pyle_openssl_error(const char *what) {
    char buf[512];
    pyle_describe(buf, sizeof(buf), what);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

/* `Except.ok v`. */
static lean_obj_res pyle_except_ok(lean_obj_arg v) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

/* `Except.error msg`, with the most recent OpenSSL error appended. */
static lean_obj_res pyle_except_error(const char *msg) {
    char buf[512];
    pyle_describe(buf, sizeof(buf), msg);
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, lean_mk_string(buf));
    return r;
}

/* A fresh Lean byte array holding a copy of `len` bytes at `data`. */
static lean_obj_res pyle_mk_bytes(const unsigned char *data, size_t len) {
    lean_object *arr = lean_alloc_sarray(1, len, len);
    if (len > 0) memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

/* ------------------------------------------------------------------ */
/* Randomness and comparison                                            */
/* ------------------------------------------------------------------ */

/* `n` bytes from the operating system's generator, through OpenSSL's DRBG. */
LEAN_EXPORT lean_obj_res pyle_random_bytes(size_t n, lean_obj_arg w) {
    (void)w;
    if (n > INT_MAX)
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("RAND_bytes: request too large")));
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

/* ------------------------------------------------------------------ */
/* Signing keys                                                         */
/* ------------------------------------------------------------------ */

/* The algorithms, numbered as `Pyle.Crypto.SigningAlgorithm.code` numbers
 * them. */
enum { PYLE_ES256 = 0, PYLE_EDDSA = 1, PYLE_RS256 = 2 };

/* Does `k` belong to algorithm `alg`?  ES256 wants a P-256 key, EdDSA an
 * Ed25519 key and RS256 an RSA key (not RSA-PSS) of at least 2048 bits. */
static int pyle_key_matches(EVP_PKEY *k, uint8_t alg) {
    switch (alg) {
    case PYLE_ES256: {
        char group[64];
        size_t len = 0;
        if (!EVP_PKEY_is_a(k, "EC")) return 0;
        if (!EVP_PKEY_get_group_name(k, group, sizeof(group), &len)) return 0;
        return strcmp(group, "prime256v1") == 0 || strcmp(group, "P-256") == 0;
    }
    case PYLE_EDDSA:
        return EVP_PKEY_is_a(k, "ED25519");
    case PYLE_RS256:
        return EVP_PKEY_is_a(k, "RSA") && EVP_PKEY_get_bits(k) >= 2048;
    default:
        return 0;
    }
}

/* Parse a PKCS#8 PrivateKeyInfo, insisting that it is the whole input and
 * that it is a key for `alg`.  On failure, returns NULL and points `why` at a
 * description. */
static EVP_PKEY *pyle_load_key(uint8_t alg, b_lean_obj_arg der, const char **why) {
    const unsigned char *p = lean_sarray_cptr(der);
    size_t len = lean_sarray_size(der);
    if (len > LONG_MAX) { *why = "private key too large"; return NULL; }
    PKCS8_PRIV_KEY_INFO *info = d2i_PKCS8_PRIV_KEY_INFO(NULL, &p, (long)len);
    if (!info || p != lean_sarray_cptr(der) + len) {
        PKCS8_PRIV_KEY_INFO_free(info);
        *why = "private key is not a DER PKCS#8 PrivateKeyInfo";
        return NULL;
    }
    EVP_PKEY *k = EVP_PKCS82PKEY(info);
    PKCS8_PRIV_KEY_INFO_free(info);
    if (!k) { *why = "private key could not be decoded"; return NULL; }
    if (!pyle_key_matches(k, alg)) {
        EVP_PKEY_free(k);
        *why = "private key does not belong to the requested algorithm";
        return NULL;
    }
    return k;
}

/* A new private key for `alg`, as a DER PKCS#8 PrivateKeyInfo. */
LEAN_EXPORT lean_obj_res pyle_key_generate(uint8_t alg, lean_obj_arg w) {
    (void)w;
    EVP_PKEY *k = NULL;
    switch (alg) {
    case PYLE_ES256: k = EVP_PKEY_Q_keygen(NULL, NULL, "EC", "P-256"); break;
    case PYLE_EDDSA: k = EVP_PKEY_Q_keygen(NULL, NULL, "ED25519"); break;
    case PYLE_RS256: k = EVP_PKEY_Q_keygen(NULL, NULL, "RSA", (size_t)2048); break;
    default:
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("key generation: unknown algorithm")));
    }
    if (!k) return pyle_openssl_error("key generation");
    PKCS8_PRIV_KEY_INFO *info = EVP_PKEY2PKCS8(k);
    EVP_PKEY_free(k);
    if (!info) return pyle_openssl_error("key generation: PKCS#8 encoding");
    unsigned char *buf = NULL;
    int n = i2d_PKCS8_PRIV_KEY_INFO(info, &buf);
    PKCS8_PRIV_KEY_INFO_free(info);
    if (n <= 0) return pyle_openssl_error("key generation: PKCS#8 encoding");
    lean_object *out = pyle_mk_bytes(buf, (size_t)n);
    OPENSSL_clear_free(buf, (size_t)n);
    return lean_io_result_mk_ok(out);
}

/* The public half of a PKCS#8 private key for `alg`: for ES256 the compressed
 * SEC1 point (33 bytes), for EdDSA the 32-byte Ed25519 key, and for RS256 the
 * DER SubjectPublicKeyInfo.  Returns an `Except String ByteArray`. */
LEAN_EXPORT lean_obj_res pyle_key_public(uint8_t alg, b_lean_obj_arg der) {
    const char *why = NULL;
    EVP_PKEY *k = pyle_load_key(alg, der, &why);
    if (!k) return pyle_except_error(why);
    lean_object *out = NULL;
    switch (alg) {
    case PYLE_ES256: {
        unsigned char pt[133];
        size_t len = 0;
        if (EVP_PKEY_get_octet_string_param(k, OSSL_PKEY_PARAM_PUB_KEY, pt, sizeof(pt), &len)) {
            if (len == 65 && pt[0] == 4) {
                pt[0] = (unsigned char)(2 | (pt[64] & 1));
                out = pyle_mk_bytes(pt, 33);
            } else if (len == 33 && (pt[0] == 2 || pt[0] == 3)) {
                out = pyle_mk_bytes(pt, 33);
            }
        }
        break;
    }
    case PYLE_EDDSA: {
        unsigned char pub[32];
        size_t len = sizeof(pub);
        if (EVP_PKEY_get_raw_public_key(k, pub, &len) && len == 32)
            out = pyle_mk_bytes(pub, 32);
        break;
    }
    case PYLE_RS256: {
        unsigned char *buf = NULL;
        int n = i2d_PUBKEY(k, &buf);
        if (n > 0) out = pyle_mk_bytes(buf, (size_t)n);
        OPENSSL_free(buf);
        break;
    }
    }
    EVP_PKEY_free(k);
    if (!out) return pyle_except_error("public key could not be encoded");
    return pyle_except_ok(out);
}

/* Sign `msg` with a PKCS#8 private key for `alg`.  ES256 signatures are DER
 * `SEQUENCE { r, s }`, EdDSA signatures are the 64 bytes of RFC 8032, and
 * RS256 signatures are RSASSA-PKCS1-v1_5 with SHA-256. */
LEAN_EXPORT lean_obj_res pyle_key_sign(uint8_t alg, b_lean_obj_arg der, b_lean_obj_arg msg,
                                       lean_obj_arg w) {
    (void)w;
    const char *why = NULL;
    EVP_PKEY *k = pyle_load_key(alg, der, &why);
    if (!k) return pyle_openssl_error(why);
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    const EVP_MD *md = alg == PYLE_EDDSA ? NULL : EVP_sha256();
    unsigned char *sig = NULL;
    size_t siglen = 0;
    lean_object *out = NULL;
    if (ctx && EVP_DigestSignInit(ctx, NULL, md, NULL, k) == 1 &&
        EVP_DigestSign(ctx, NULL, &siglen, lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1 &&
        (sig = OPENSSL_malloc(siglen)) != NULL &&
        EVP_DigestSign(ctx, sig, &siglen, lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1)
        out = pyle_mk_bytes(sig, siglen);
    OPENSSL_free(sig);
    EVP_MD_CTX_free(ctx);
    EVP_PKEY_free(k);
    if (!out) return pyle_openssl_error("signing");
    return lean_io_result_mk_ok(out);
}

/* Parse a DER SubjectPublicKeyInfo holding an RSA key of at least 2048 bits,
 * insisting that it is the whole input. */
static EVP_PKEY *pyle_load_rsa_public(b_lean_obj_arg spki) {
    const unsigned char *p = lean_sarray_cptr(spki);
    size_t len = lean_sarray_size(spki);
    if (len > LONG_MAX) return NULL;
    EVP_PKEY *k = d2i_PUBKEY(NULL, &p, (long)len);
    if (k && (p != lean_sarray_cptr(spki) + len || !pyle_key_matches(k, PYLE_RS256))) {
        EVP_PKEY_free(k);
        k = NULL;
    }
    return k;
}

/* Does `sig` verify as an RSASSA-PKCS1-v1_5 SHA-256 signature on `msg` under
 * the RSA public key `spki`?  Every input is public; this lives here only
 * because pyle has no RSA in Lean. */
LEAN_EXPORT uint8_t pyle_rs256_verify(b_lean_obj_arg spki, b_lean_obj_arg msg,
                                      b_lean_obj_arg sig) {
    EVP_PKEY *k = pyle_load_rsa_public(spki);
    if (!k) { ERR_clear_error(); return 0; }
    EVP_MD_CTX *ctx = EVP_MD_CTX_new();
    int ok = ctx && EVP_DigestVerifyInit(ctx, NULL, EVP_sha256(), NULL, k) == 1 &&
        EVP_DigestVerify(ctx, lean_sarray_cptr(sig), lean_sarray_size(sig),
                         lean_sarray_cptr(msg), lean_sarray_size(msg)) == 1;
    EVP_MD_CTX_free(ctx);
    EVP_PKEY_free(k);
    ERR_clear_error();
    return ok ? 1 : 0;
}

/* The big-endian modulus and public exponent of an RSA SubjectPublicKeyInfo,
 * for publishing it as a JWK.  Returns an `Except String (ByteArray ×
 * ByteArray)`. */
LEAN_EXPORT lean_obj_res pyle_rsa_public_numbers(b_lean_obj_arg spki) {
    EVP_PKEY *k = pyle_load_rsa_public(spki);
    if (!k) return pyle_except_error("not an RSA SubjectPublicKeyInfo of at least 2048 bits");
    BIGNUM *n = NULL, *e = NULL;
    lean_object *res = NULL;
    if (EVP_PKEY_get_bn_param(k, OSSL_PKEY_PARAM_RSA_N, &n) &&
        EVP_PKEY_get_bn_param(k, OSSL_PKEY_PARAM_RSA_E, &e)) {
        lean_object *nb = lean_alloc_sarray(1, BN_num_bytes(n), BN_num_bytes(n));
        lean_object *eb = lean_alloc_sarray(1, BN_num_bytes(e), BN_num_bytes(e));
        BN_bn2bin(n, lean_sarray_cptr(nb));
        BN_bn2bin(e, lean_sarray_cptr(eb));
        res = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(res, 0, nb);
        lean_ctor_set(res, 1, eb);
    }
    BN_free(n);
    BN_free(e);
    EVP_PKEY_free(k);
    if (!res) return pyle_except_error("RSA public numbers");
    return pyle_except_ok(res);
}

/* ------------------------------------------------------------------ */
/* ChaCha20-Poly1305                                                    */
/* ------------------------------------------------------------------ */

#define PYLE_AEAD_KEY 32
#define PYLE_AEAD_NONCE 12
#define PYLE_AEAD_TAG 16

/* RFC 8439 ChaCha20-Poly1305 of `pt` with associated data `ad` under `key`
 * and `nonce`, written as `nonce ‖ ciphertext ‖ tag`.  The caller chooses the
 * nonce, so the caller is responsible for never repeating one under a key.
 * Returns an `Except String ByteArray`. */
LEAN_EXPORT lean_obj_res pyle_aead_seal(b_lean_obj_arg key, b_lean_obj_arg nonce,
                                        b_lean_obj_arg ad, b_lean_obj_arg pt) {
    size_t adlen = lean_sarray_size(ad), ptlen = lean_sarray_size(pt);
    if (lean_sarray_size(key) != PYLE_AEAD_KEY)
        return pyle_except_error("seal: the key must be 32 bytes");
    if (lean_sarray_size(nonce) != PYLE_AEAD_NONCE)
        return pyle_except_error("seal: the nonce must be 12 bytes");
    if (adlen > INT_MAX || ptlen > INT_MAX - PYLE_AEAD_NONCE - PYLE_AEAD_TAG)
        return pyle_except_error("seal: input too large");
    size_t total = PYLE_AEAD_NONCE + ptlen + PYLE_AEAD_TAG;
    lean_object *out = lean_alloc_sarray(1, total, total);
    unsigned char *o = lean_sarray_cptr(out);
    memcpy(o, lean_sarray_cptr(nonce), PYLE_AEAD_NONCE);
    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    int len = 0;
    int ok = ctx &&
        EVP_EncryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, lean_sarray_cptr(key),
                           lean_sarray_cptr(nonce)) == 1 &&
        (adlen == 0 ||
         EVP_EncryptUpdate(ctx, NULL, &len, lean_sarray_cptr(ad), (int)adlen) == 1) &&
        (ptlen == 0 ||
         EVP_EncryptUpdate(ctx, o + PYLE_AEAD_NONCE, &len, lean_sarray_cptr(pt), (int)ptlen) == 1) &&
        EVP_EncryptFinal_ex(ctx, o + PYLE_AEAD_NONCE + ptlen, &len) == 1 &&
        EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_GET_TAG, PYLE_AEAD_TAG,
                            o + PYLE_AEAD_NONCE + ptlen) == 1;
    EVP_CIPHER_CTX_free(ctx);
    if (!ok) {
        lean_dec(out);
        return pyle_except_error("seal");
    }
    return pyle_except_ok(out);
}

/* The inverse of pyle_aead_seal: split `sealed` into nonce, ciphertext and
 * tag, and return the plaintext only if the tag authenticates both it and
 * `ad`.  A plaintext that fails to authenticate is wiped, never returned.
 * Returns an `Except String ByteArray`. */
LEAN_EXPORT lean_obj_res pyle_aead_open(b_lean_obj_arg key, b_lean_obj_arg ad,
                                        b_lean_obj_arg sealed) {
    size_t adlen = lean_sarray_size(ad), slen = lean_sarray_size(sealed);
    if (lean_sarray_size(key) != PYLE_AEAD_KEY)
        return pyle_except_error("open: the key must be 32 bytes");
    if (slen < PYLE_AEAD_NONCE + PYLE_AEAD_TAG)
        return pyle_except_error("open: the sealed value is too short");
    if (adlen > INT_MAX || slen > INT_MAX)
        return pyle_except_error("open: input too large");
    const unsigned char *s = lean_sarray_cptr(sealed);
    size_t ctlen = slen - PYLE_AEAD_NONCE - PYLE_AEAD_TAG;
    lean_object *out = lean_alloc_sarray(1, ctlen, ctlen);
    unsigned char *o = lean_sarray_cptr(out);
    unsigned char tag[PYLE_AEAD_TAG];
    memcpy(tag, s + PYLE_AEAD_NONCE + ctlen, PYLE_AEAD_TAG);
    EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
    int len = 0;
    int ok = ctx &&
        EVP_DecryptInit_ex(ctx, EVP_chacha20_poly1305(), NULL, lean_sarray_cptr(key), s) == 1 &&
        (adlen == 0 ||
         EVP_DecryptUpdate(ctx, NULL, &len, lean_sarray_cptr(ad), (int)adlen) == 1) &&
        (ctlen == 0 ||
         EVP_DecryptUpdate(ctx, o, &len, s + PYLE_AEAD_NONCE, (int)ctlen) == 1) &&
        EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_AEAD_SET_TAG, PYLE_AEAD_TAG, tag) == 1 &&
        EVP_DecryptFinal_ex(ctx, o + ctlen, &len) == 1;
    EVP_CIPHER_CTX_free(ctx);
    if (!ok) {
        OPENSSL_cleanse(o, ctlen);
        lean_dec(out);
        ERR_clear_error();
        return pyle_except_error("open: authentication failed");
    }
    return pyle_except_ok(out);
}

/* ------------------------------------------------------------------ */
/* Argon2id                                                             */
/* ------------------------------------------------------------------ */

/* Argon2id (RFC 9106, version 0x13) of `pass` with `salt`, the optional
 * `secret` and associated data `ad`, `iter` passes over `memcost` KiB in
 * `lanes` lanes, giving `outlen` bytes.
 *
 * The KDF is fetched by name rather than through the OSSL_KDF_NAME_ARGON2ID
 * and OSSL_KDF_PARAM_ARGON2_* macros, which 3.0's headers lack: what matters
 * is whether the library linked in at run time provides it, and the
 * toolchain's does.  The computation runs in one thread; the lanes are still
 * `lanes`, so the result is the same as with more threads. */
LEAN_EXPORT lean_obj_res pyle_argon2id(b_lean_obj_arg pass, b_lean_obj_arg salt,
                                       b_lean_obj_arg secret, b_lean_obj_arg ad,
                                       uint32_t iter, uint32_t memcost, uint32_t lanes,
                                       uint32_t outlen, lean_obj_arg w) {
    (void)w;
    EVP_KDF *kdf = EVP_KDF_fetch(NULL, "ARGON2ID", NULL);
    if (!kdf)
        return pyle_openssl_error(
            "Argon2id is unavailable: the linked OpenSSL does not provide it "
            "(it needs OpenSSL 3.2 or later)");
    EVP_KDF_CTX *kctx = EVP_KDF_CTX_new(kdf);
    EVP_KDF_free(kdf);
    if (!kctx) return pyle_openssl_error("Argon2id");
    uint32_t threads = 1;
    OSSL_PARAM params[9], *p = params;
    *p++ = OSSL_PARAM_construct_octet_string("pass", (void *)lean_sarray_cptr(pass),
                                             lean_sarray_size(pass));
    *p++ = OSSL_PARAM_construct_octet_string("salt", (void *)lean_sarray_cptr(salt),
                                             lean_sarray_size(salt));
    if (lean_sarray_size(secret) > 0)
        *p++ = OSSL_PARAM_construct_octet_string("secret", (void *)lean_sarray_cptr(secret),
                                                 lean_sarray_size(secret));
    if (lean_sarray_size(ad) > 0)
        *p++ = OSSL_PARAM_construct_octet_string("ad", (void *)lean_sarray_cptr(ad),
                                                 lean_sarray_size(ad));
    *p++ = OSSL_PARAM_construct_uint32("iter", &iter);
    *p++ = OSSL_PARAM_construct_uint32("memcost", &memcost);
    *p++ = OSSL_PARAM_construct_uint32("lanes", &lanes);
    *p++ = OSSL_PARAM_construct_uint32("threads", &threads);
    *p = OSSL_PARAM_construct_end();
    lean_object *out = lean_alloc_sarray(1, outlen, outlen);
    int ok = EVP_KDF_derive(kctx, lean_sarray_cptr(out), outlen, params) == 1;
    EVP_KDF_CTX_free(kctx);
    if (!ok) {
        lean_dec(out);
        return pyle_openssl_error("Argon2id");
    }
    return lean_io_result_mk_ok(out);
}

/* ------------------------------------------------------------------ */
/* X.509                                                                */
/* ------------------------------------------------------------------ */

/* Parse one DER certificate, insisting that it is the whole input. */
static X509 *pyle_load_cert(b_lean_obj_arg der) {
    const unsigned char *p = lean_sarray_cptr(der);
    size_t len = lean_sarray_size(der);
    if (len > LONG_MAX) return NULL;
    X509 *c = d2i_X509(NULL, &p, (long)len);
    if (c && p != lean_sarray_cptr(der) + len) {
        X509_free(c);
        c = NULL;
    }
    return c;
}

/* Verify the certificate chain `chain` (an `Array ByteArray` of DER
 * certificates, leaf first, the rest untrusted intermediates in any order)
 * against the trust anchors `roots`, at the current time or, if `at_time` is
 * set, at the Unix time `time`.  Every input is public: this is here because
 * X.509 path validation is not something to rewrite.  Returns an
 * `IO (Except String Unit)`. */
LEAN_EXPORT lean_obj_res pyle_x509_verify(b_lean_obj_arg chain, b_lean_obj_arg roots,
                                          uint8_t at_time, uint64_t time, lean_obj_arg w) {
    (void)w;
    size_t nchain = lean_array_size(chain), nroots = lean_array_size(roots);
    if (nchain == 0)
        return lean_io_result_mk_ok(pyle_except_error("the certificate chain is empty"));
    X509_STORE *store = X509_STORE_new();
    STACK_OF(X509) *untrusted = sk_X509_new_null();
    X509_STORE_CTX *ctx = X509_STORE_CTX_new();
    X509 *leaf = NULL;
    const char *why = NULL;
    char reason[256];
    if (!store || !untrusted || !ctx) { why = "out of memory"; goto done; }
    for (size_t i = 0; i < nroots; i++) {
        X509 *c = pyle_load_cert(lean_array_get_core(roots, i));
        if (!c) { why = "a root certificate is not valid DER"; goto done; }
        int added = X509_STORE_add_cert(store, c);
        X509_free(c);
        if (!added) { why = "a root certificate could not be added"; goto done; }
    }
    leaf = pyle_load_cert(lean_array_get_core(chain, 0));
    if (!leaf) { why = "the leaf certificate is not valid DER"; goto done; }
    for (size_t i = 1; i < nchain; i++) {
        X509 *c = pyle_load_cert(lean_array_get_core(chain, i));
        if (!c || !sk_X509_push(untrusted, c)) {
            X509_free(c);
            why = "an intermediate certificate is not valid DER";
            goto done;
        }
    }
    if (X509_STORE_CTX_init(ctx, store, leaf, untrusted) != 1) {
        why = "the verification context could not be set up";
        goto done;
    }
    if (at_time) X509_VERIFY_PARAM_set_time(X509_STORE_CTX_get0_param(ctx), (time_t)time);
    if (X509_verify_cert(ctx) != 1) {
        snprintf(reason, sizeof(reason), "certificate chain rejected: %s",
                 X509_verify_cert_error_string(X509_STORE_CTX_get_error(ctx)));
        why = reason;
    }
done:
    X509_STORE_CTX_free(ctx);
    X509_free(leaf);
    sk_X509_pop_free(untrusted, X509_free);
    X509_STORE_free(store);
    ERR_clear_error();
    if (why) return lean_io_result_mk_ok(pyle_except_error(why));
    return lean_io_result_mk_ok(pyle_except_ok(lean_box(0)));
}