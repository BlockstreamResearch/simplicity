/**********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                             *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_UTIL_H
#define SECP256K1_UTIL_H

#include <stdalign.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

typedef struct {
    void (*fn)(const char *text, void* data);
    const void* data;
} secp256k1_callback;

static SECP256K1_INLINE void secp256k1_callback_call(const secp256k1_callback * const cb, const char * const text) {
    cb->fn(text, (void*)(uintptr_t)cb->data);
}

#ifdef DETERMINISTIC
#define TEST_FAILURE(msg) do { \
    fprintf(stderr, "%s\n", msg); \
    abort(); \
} while(0);
#else
#define TEST_FAILURE(msg) do { \
    fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, msg); \
    abort(); \
} while(0)
#endif

#if SECP256K1_GNUC_PREREQ(3, 0)
#define EXPECT(x,c) __builtin_expect((x),(c))
#else
#define EXPECT(x,c) (x)
#endif

#ifdef DETERMINISTIC
#define CHECK(cond) do { \
    if (EXPECT(!(cond), 0)) { \
        TEST_FAILURE("test condition failed"); \
    } \
} while(0)
#else
#define CHECK(cond) do { \
    if (EXPECT(!(cond), 0)) { \
        TEST_FAILURE("test condition failed: " #cond); \
    } \
} while(0)
#endif

/* Like assert(), but when VERIFY is defined, and side-effect safe. */
#if defined(COVERAGE)
#define VERIFY_CHECK(check)
#define VERIFY_SETUP(stmt)
#elif defined(VERIFY)
#define VERIFY_CHECK CHECK
#define VERIFY_SETUP(stmt) do { stmt; } while(0)
#else
#define VERIFY_CHECK(cond) do { (void)(cond); } while(0)
#define VERIFY_SETUP(stmt)
#endif

#define ALIGNMENT (alignof(max_align_t))

#define ROUND_TO_ALIGN(size) (((size + ALIGNMENT - 1) / ALIGNMENT) * ALIGNMENT)

/* Assume there is a contiguous memory object with bounds [base, base + max_size)
 * of which the memory range [base, *prealloc_ptr) is already allocated for usage,
 * where *prealloc_ptr is an aligned pointer. In that setting, this functions
 * reserves the subobject [*prealloc_ptr, *prealloc_ptr + alloc_size) of
 * alloc_size bytes by increasing *prealloc_ptr accordingly, taking into account
 * alignment requirements.
 *
 * The function returns an aligned pointer to the newly allocated subobject.
 *
 * This is useful for manual memory management: if we're simply given a block
 * [base, base + max_size), the caller can use this function to allocate memory
 * in this block and keep track of the current allocation state with *prealloc_ptr.
 *
 * It is VERIFY_CHECKed that there is enough space left in the memory object and
 * *prealloc_ptr is aligned relative to base.
 */
static SECP256K1_INLINE void *manual_alloc(void** prealloc_ptr, size_t alloc_size, void* base, size_t max_size) {
    size_t aligned_alloc_size = ROUND_TO_ALIGN(alloc_size);
    void* ret;
    VERIFY_CHECK(prealloc_ptr != NULL);
    VERIFY_CHECK(*prealloc_ptr != NULL);
    VERIFY_CHECK(base != NULL);
    VERIFY_CHECK((unsigned char*)*prealloc_ptr >= (unsigned char*)base);
    VERIFY_CHECK(((unsigned char*)*prealloc_ptr - (unsigned char*)base) % ALIGNMENT == 0);
    VERIFY_CHECK((unsigned char*)*prealloc_ptr - (unsigned char*)base + aligned_alloc_size <= max_size);
    ret = *prealloc_ptr;
    *((unsigned char**)prealloc_ptr) += aligned_alloc_size;
    return ret;
}

/* Macro for restrict, when not in a VERIFY build. */
#if defined(SECP256K1_BUILD) && defined(VERIFY)
# define SECP256K1_RESTRICT
#else
# define SECP256K1_RESTRICT restrict
#endif


#endif /* SECP256K1_UTIL_H */
