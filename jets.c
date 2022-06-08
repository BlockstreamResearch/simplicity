#include "jets.h"
#include "sha256.h"

/* low_32 : ONE |- TWO^32 */
bool low_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // env is unused;
  write32(dst, 0);
  return true;
}

/* one_32 : ONE |- TWO^32 */
bool one_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // env is unused;
  write32(dst, 1);
  return true;
}

bool add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, 0xFFFFFFFF - y < x);
  /* <pedantic>
   * Multiplying a uint32_t by 1U promotes a value's type to the wider of unsigned int and uint32_t,
   * avoiding any possible issues with signed integer promotions causing havoc with unsigned modular arithmetic
   * if int happens to be 33 bits wide.
   * </pedantic>
   */
  write32(dst, 1U * x + y);
  return true;
}

bool full_add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  bool z = readBit(&src);
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, 0xFFFFFFFF - y < x || 0xFFFFFFFF - z < x + y);
  /* <pedantic>
   * Multiplying a uint32_t by 1U promotes a value's type to the wider of unsigned int and uint32_t,
   * avoiding any possible issues with signed integer promotions causing havoc with unsigned modular arithmetic
   * if int happens to be 33 bits wide.
   * </pedantic>
   */
  write32(dst, 1U * x + y + z);
  return true;
}

bool subtract_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x < y);
  write32(dst, x - y);
  return true;
}

bool full_subtract_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  bool z = readBit(&src);
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x < y || x - y < z);
  write32(dst, x - y - z);
  return true;
}

bool multiply_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast64_t x = read32(&src);
  uint_fast64_t y = read32(&src);
  write64(dst, x * y);
  return true;
}

bool full_multiply_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast64_t x = read32(&src);
  uint_fast64_t y = read32(&src);
  uint_fast64_t z = read32(&src);
  uint_fast64_t w = read32(&src);
  write64(dst, x * y + z + w);
  return true;
}

/* eq_32 : TWO^32 * TWO^32 |- TWO */
bool eq_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t x = read32(&src);
  uint_fast32_t y = read32(&src);
  writeBit(dst, x == y);
  return true;
}

/* sha_256_iv : ONE |- TWO^256 */
bool sha_256_iv(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // env is unused;

  uint32_t iv[8];
  sha256_iv(iv);

  write32s(dst, iv, 8);
  return true;
}

/* sha_256_block : TWO^256 * TWO^512 |- TWO^256 */
bool sha_256_block(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint32_t h[8];
  uint32_t block[16];
  read32s(h, 8, &src);
  read32s(block, 16, &src);
  sha256_compression(h, block);
  write32s(dst, h, 8);
  return true;
}

/* Read bytes from a Simplicity buffer of type (TWO^8)^<2^(n+1) into 'buf'.
 * Set 'len' to the number of bytes read from the buffer.
 * Advance the 'src' frame to the end of the buffer type.
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: unsigned char buf[2^(n+1)-1];
 *               NULL != len;
 *               '*src' is a valid read frame for 8*(2^(n+1)-1)+n+1 more cells;
 *               0 <= n < 16
 */
static void read_buffer8(unsigned char* buf, size_t* len, frameItem* src, int n) {
  assert(0 <= n && n < 16);
  *len = 0;

  for (size_t i = (size_t)1 << n; 0 < i; i /= 2) {
    if (readBit(src)) {
      read8s(buf, i, src);
      buf += i; *len += i;
    } else {
      forwardBits(src, i*8);
    }
  }
}

/* Write 'len' bytes to a Simplicity buffer of type (TWO^8)^<2^(n+1) from 'buf'.
 * Advance the 'dst' frame to the end of the buffer type.
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: '*dst' is a valid write frame for 8*(2^(n+1)-1)+n+1 more cells;
 *               unsigned char buf[len];
 *               len < 2^(n+1);
 *               0 <= n < 16;
 */
static void write_buffer8(frameItem* dst, const unsigned char* buf, size_t len, int n) {
  assert(0 <= n && n < 16);
  assert(len < ((size_t)1<<(n+1)));
  for (size_t i = (size_t)1 << n; 0 < i; i /= 2) {
    if (writeBit(dst, i <= len)) {
      write8s(dst, buf, i);
      buf += i; len -= i;
    } else {
      skipBits(dst, i*8);
    }
  }
}

/* Read data from a Simplicity CTX8 type (TWO^8)^<2^64 * TWO^64 * TWO^256 and fill in a sha256_context value.
 * Advance the 'src' frame to the end of the CTX8 type.
 * Returns false if the context's counter is too large (i.e. the compression count is greater than or equal to 2^55).
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: NULL != ctx->output;
 *               '*src' is a valid read frame for 838 more cells;
 */
static bool read_sha256_context(sha256_context* ctx, frameItem* src) {
  size_t len;
  uint_fast64_t compressionCount;

  read_buffer8(ctx->block, &len, src, 5);
  compressionCount = read64(src);
  ctx->counter = ((compressionCount*1U) << 6) + len;
  read32s(ctx->output, 8, src);

  return (ctx->counter <= 0x1fffffffffffffff && ctx->counter >> 6 == compressionCount);
}

/* Write data to a Simplicity CTX8 type (TWO^8)^<2^64 * TWO^64 * TWO^256 from a sha256_context value.
 * Advance the 'dst' frame to the end of the CTX8 type.
 *
 * The notation X^<2 is notation for the type (S X)
 * The notation X^<(2*n) is notation for the type S (X^n) * X^<n
 *
 * Precondition: '*dst' is a valid write frame for 838 more cells;
 *               NULL != ctx->output;
 *               ctx->counter < 2^61;
 */
static void write_sha256_context(frameItem* dst, const sha256_context* ctx) {
  assert(ctx->counter <= 0x1fffffffffffffff);
  write_buffer8(dst, ctx->block, ctx->counter % 64, 5);
  write64(dst, ctx->counter >> 6);
  write32s(dst, ctx->output, 8);
}

/* sha_256_ctx_8_init : ONE |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_init(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  (void) src; // env is unused;

  uint32_t iv[8];
  sha256_context ctx = sha256_init(iv);

  write_sha256_context(dst, &ctx);
  return true;
}

/* sha_256_ctx_8_add_n : CTX8 * (TWO^8)^n |- CTX8
 * where
 * n is a power of 2 less than or equal to 512
 * and
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
static bool sha_256_ctx_8_add_n(frameItem* dst, frameItem *src, size_t n) {
  assert(0 < n && n <= 512 && (n & (n - 1)) == 0);
  sha256_midstate midstate;
  unsigned char buf[512];
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, src)) return false;
  if (0x1fffffffffffffff - ctx.counter < n) return false;

  read8s(buf, n, src);
  sha256_uchars(&ctx, buf, n);
  write_sha256_context(dst, &ctx);
  return true;
}

/* sha_256_ctx_8_add_1 : CTX8 * TWO^8 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_1(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 1);
}

/* sha_256_ctx_8_add_2 : CTX8 * (TWO^8)^2 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_2(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 2);
}

/* sha_256_ctx_8_add_4 : CTX8 * (TWO^8)^4 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_4(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 4);
}

/* sha_256_ctx_8_add_8 : CTX8 * (TWO^8)^8 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_8(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 8);
}

/* sha_256_ctx_8_add_16 : CTX8 * (TWO^8)^16 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_16(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 16);
}

/* sha_256_ctx_8_add_32 : CTX8 * (TWO^8)^32 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_32(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 32);
}

/* sha_256_ctx_8_add_64 : CTX8 * (TWO^8)^64 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_64(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 64);
}

/* sha_256_ctx_8_add_128 : CTX8 * (TWO^8)^128 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_128(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 128);
}

/* sha_256_ctx_8_add_256 : CTX8 * (TWO^8)^256 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_256(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 256);
}

/* sha_256_ctx_8_add_512 : CTX8 * (TWO^8)^512 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_512(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  return sha_256_ctx_8_add_n(dst, &src, 512);
}

/* sha_256_ctx_8_add_buffer_511 : CTX8 * (TWO^8)^<512 |- CTX8
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_add_buffer_511(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  sha256_midstate midstate;
  unsigned char buf[511];
  size_t buf_len;
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, &src)) return false;

  read_buffer8(buf, &buf_len, &src, 8);
  if (0x1fffffffffffffff - ctx.counter < buf_len) return false;

  sha256_uchars(&ctx, buf, buf_len);
  write_sha256_context(dst, &ctx);
  return true;
}

/* sha_256_ctx_8_finalize : CTX8 |- TWO^256
 * where
 * CTX8 = (TWO^8)^<64 * TWO^64 * TWO^256
 */
bool sha_256_ctx_8_finalize(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  sha256_midstate midstate;
  sha256_context ctx = {.output = midstate.s};

  if (!read_sha256_context(&ctx, &src)) return false;

  sha256_finalize(&ctx);
  write32s(dst, midstate.s, 8);
  return true;
}

/* parse_sequence : TWO^32 |- TWO^32 + TWO^32 */
bool parse_lock(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t nLockTime = read32(&src);
  writeBit(dst, 500000000U <= nLockTime);
  write32(dst, nLockTime);
  return true;
}

/* parse_sequence : TWO^32 |- S (TWO^16 + TWO^16) */
bool parse_sequence(frameItem* dst, frameItem src, const txEnv* env) {
  (void) env; // env is unused;
  uint_fast32_t nSequence = read32(&src);
  if (writeBit(dst, nSequence < ((uint_fast32_t)1 << 31))) {
    writeBit(dst, nSequence & ((uint_fast32_t)1 << 22));
    write16(dst, nSequence & 0xffff);
  } else {
    skipBits(dst, 17);
  }
  return true;
}
