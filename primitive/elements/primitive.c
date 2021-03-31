/* This module implements the 'primitive.h' interface for the Elements application of Simplicity.
 */
#include "primitive.h"

#include "jets.h"
#include "../../callonce.h"
#include "../../prefix.h"
#include "../../tag.h"
#include "../../unreachable.h"

#define PRIMITIVE_TAG(s) SIMPLICITY_PREFIX "\x1F" "Primitive\x1F" "Elements\x1F" s
#define JET_TAG SIMPLICITY_PREFIX "\x1F" "Jet"

/* An enumeration of all the types we need to construct to specify the input and output types of all jets created by 'decodeJet'. */
enum TypeNamesForJets {
  one,
  two,
  word2,
  word4,
  word8,
  word16,
  word32,
  word64,
  word128,
  word256,
  word512,
  pubkey,
  sTwo,
  outpnt,
  sOutpnt,
  confWord256,
  sConfWord256,
  sSConfWord256,
  confWord64,
  sConfWord64,
  sSConfWord64,
  sWord256,
  sSWord256,
  sWord32,
  word2TimesWord256,
  twoPlusWord4,
  word2TimesWord256PlusTwoPlusWord4,
  sWord2TimesWord256PlusTwoPlusWord4,
  sSWord2TimesWord256PlusTwoPlusWord4,
  twoTimesWord32,
  twoTimesWord64,
  word256TimesWord512,
  NumberOfTypeNames
};

/* Allocate a fresh set of unification variables bound to at least all the types necessary
 * for all the jets that can be created by 'decodeJet', and also the type 'TWO^256',
 * and also allocate space for 'extra_var_len' many unification variables.
 * Return the number of non-trivial bindings created.
 *
 * However, if malloc fails, then return 0.
 *
 * Precondition: NULL != bound_var;
 *               NULL != word256_ix;
 *               NULL != extra_var_start;
 *
 * Postcondition: Either '*bound_var == NULL' and the function returns 0
 *                or 'unification_var (*bound_var)[*extra_var_start + extra_var_len]' is an array of unification variables
 *                   such that for any 'jet : A |- B' there is some 'i < *extra_var_start' and 'j < *extra_var_start' such that
 *                      '(*bound_var)[i]' is bound to 'A' and '(*bound_var)[j]' is bound to 'B'
 *                   and, '*word256_ix < *extra_var_start' and '(*bound_var)[*word256_ix]' is bound the type 'TWO^256'
 */
size_t mallocBoundVars(unification_var** bound_var, size_t* word256_ix, size_t* extra_var_start, size_t extra_var_len) {
  _Static_assert(NumberOfTypeNames <= SIZE_MAX / sizeof(unification_var), "NumberOfTypeNames is too large");
  *bound_var = extra_var_len <= SIZE_MAX / sizeof(unification_var) - NumberOfTypeNames
             ? malloc((NumberOfTypeNames + extra_var_len) * sizeof(unification_var))
             : NULL;
  if (!(*bound_var)) return 0;
  (*bound_var)[one] = (unification_var){ .isBound = true,
      .bound = { .kind = ONE } };
  (*bound_var)[two] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[one] } } };
  (*bound_var)[word2] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[two] } } };
  (*bound_var)[word4] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word2], &(*bound_var)[word2] } } };
  (*bound_var)[word8] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word4], &(*bound_var)[word4] } } };
  (*bound_var)[word16] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word8], &(*bound_var)[word8] } } };
  (*bound_var)[word32] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word16], &(*bound_var)[word16] } } };
  (*bound_var)[word64] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word32], &(*bound_var)[word32] } } };
  (*bound_var)[word128] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word64], &(*bound_var)[word64] } } };
  (*bound_var)[word256] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word128], &(*bound_var)[word128] } } };
  (*bound_var)[word512] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word256] } } };
  (*bound_var)[pubkey] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word256] } } };
  (*bound_var)[sTwo] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[two] } } };
  (*bound_var)[outpnt] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word32] } } };
  (*bound_var)[sOutpnt] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[outpnt] } } };
  (*bound_var)[confWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[pubkey], &(*bound_var)[word256] } } };
  (*bound_var)[sConfWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[confWord256] } } };
  (*bound_var)[sSConfWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sConfWord256] } } };
  (*bound_var)[confWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[pubkey], &(*bound_var)[word64] } } };
  (*bound_var)[sConfWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[confWord64] } } };
  (*bound_var)[sSConfWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sConfWord64] } } };
  (*bound_var)[sWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word256] } } };
  (*bound_var)[sSWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sWord256] } } };
  (*bound_var)[sWord32] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word32] } } };
  (*bound_var)[word2TimesWord256] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word2], &(*bound_var)[word256] } } };
  (*bound_var)[twoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[two], &(*bound_var)[word4] } } };
  (*bound_var)[word2TimesWord256PlusTwoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM, .arg = { &(*bound_var)[word2TimesWord256], &(*bound_var)[twoPlusWord4] } } };
  (*bound_var)[sWord2TimesWord256PlusTwoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[word2TimesWord256PlusTwoPlusWord4] } } };
  (*bound_var)[sSWord2TimesWord256PlusTwoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sWord2TimesWord256PlusTwoPlusWord4] } } };
  (*bound_var)[twoTimesWord32] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word32] } } };
  (*bound_var)[twoTimesWord64] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[two], &(*bound_var)[word64] } } };
  (*bound_var)[word256TimesWord512] = (unification_var){ .isBound = true,
      .bound = { .kind = PRODUCT, .arg = { &(*bound_var)[word256], &(*bound_var)[word512] } } };

  *word256_ix = word256;
  *extra_var_start = NumberOfTypeNames;

  /* 'one' is a trivial binding, so we made 'NumberOfTypeNames - 1' non-trivial bindings. */
  return NumberOfTypeNames - 1;
};

/* An enumeration of the names of Elements specific jets and primitives. */
typedef enum jetName
{ ADD_32
, SUBTRACT_32
, MULTIPLY_32
, FULL_ADD_32
, FULL_SUBTRACT_32
, FULL_MULTIPLY_32
, SHA_256_BLOCK
, VERSION
, LOCKTIME
, INPUTISPEGIN
, INPUTPREVOUTPOINT
, INPUTASSET
, INPUTAMOUNT
, INPUTSCRIPTHASH
, INPUTSEQUENCE
, INPUTISSUANCEBLINDING
, INPUTISSUANCECONTRACT
, INPUTISSUANCEENTROPY
, INPUTISSUANCEASSETAMT
, INPUTISSUANCETOKENAMT
, OUTPUTASSET
, OUTPUTAMOUNT
, OUTPUTNONCE
, OUTPUTSCRIPTHASH
, OUTPUTNULLDATUM
, SCRIPTCMR
, CURRENTINDEX
, CURRENTISPEGIN
, CURRENTPREVOUTPOINT
, CURRENTASSET
, CURRENTAMOUNT
, CURRENTSCRIPTHASH
, CURRENTSEQUENCE
, CURRENTISSUANCEBLINDING
, CURRENTISSUANCECONTRACT
, CURRENTISSUANCEENTROPY
, CURRENTISSUANCEASSETAMT
, CURRENTISSUANCETOKENAMT
, INPUTSHASH
, OUTPUTSHASH
, NUMINPUTS
, NUMOUTPUTS
, FEE
, NUMBER_OF_JET_NAMES
} jetName;

static int32_t either(jetName* result, jetName a, jetName b, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  *result = bit ? b : a;
  return 0;
}

/* Decode an Elements specific jet name from 'stream' into 'result'.
 * All jets begin with a bit prefix of '1' which needs to have already been consumed from the 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'result' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodePrimitive(jetName* result, bitstream* stream) {
  int32_t bit = getBit(stream);
  if (bit < 0) return bit;
  if (!bit) {
    int32_t code = getNBits(5, stream);
    if (code < 0) return code;

    switch (code) {
     case 0x0: return either(result, VERSION, LOCKTIME, stream);
     case 0x1: *result = INPUTISPEGIN; return 0;
     case 0x2: *result = INPUTPREVOUTPOINT; return 0;
     case 0x3: *result = INPUTASSET; return 0;
     case 0x4: return either(result, INPUTAMOUNT, INPUTSCRIPTHASH, stream);
     case 0x5: *result = INPUTSEQUENCE; return 0;
     case 0x6: *result = INPUTISSUANCEBLINDING; return 0;
     case 0x7: *result = INPUTISSUANCECONTRACT; return 0;
     case 0x8: return either(result, INPUTISSUANCEENTROPY, INPUTISSUANCEASSETAMT, stream);
     case 0x9: *result = INPUTISSUANCETOKENAMT; return 0;
     case 0xa: *result = OUTPUTASSET; return 0;
     case 0xb: *result = OUTPUTAMOUNT; return 0;
     case 0xc: return either(result, OUTPUTNONCE, OUTPUTSCRIPTHASH, stream);
     case 0xd: *result = OUTPUTNULLDATUM; return 0;
     case 0xe: *result = SCRIPTCMR; return 0;
     case 0xf: *result = CURRENTINDEX; return 0;
     case 0x10: *result = CURRENTISPEGIN; return 0;
     case 0x11: *result = CURRENTPREVOUTPOINT; return 0;
     case 0x12: *result = CURRENTASSET; return 0;
     case 0x13: *result = CURRENTAMOUNT; return 0;
     case 0x14: *result = CURRENTSCRIPTHASH; return 0;
     case 0x15: *result = CURRENTSEQUENCE; return 0;
     case 0x16: *result = CURRENTISSUANCEBLINDING; return 0;
     case 0x17: *result = CURRENTISSUANCECONTRACT; return 0;
     case 0x18: *result = CURRENTISSUANCEENTROPY; return 0;
     case 0x19: *result = CURRENTISSUANCEASSETAMT; return 0;
     case 0x1a: *result = CURRENTISSUANCETOKENAMT; return 0;
     case 0x1b: *result = INPUTSHASH; return 0;
     case 0x1c: *result = OUTPUTSHASH; return 0;
     case 0x1d: *result = NUMINPUTS; return 0;
     case 0x1e: *result = NUMOUTPUTS; return 0;
     case 0x1f:
      /* FEE is not yet implemented.  Disable it. */
      *result = FEE; return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
    }
    assert(false);
    UNREACHABLE;
  } else {
    bit = getBit(stream);
    if (bit < 0) return bit;
    if (!bit) {
      /* Core jets */
      int32_t code = decodeUptoMaxInt(stream);
      if (code < 0) return code;

      switch (code) {
       case 2: /* Arith jets chapter */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;

        switch (code) {
         case 2: /* FullAdd */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 5: *result = FULL_ADD_32; return 0;
          }
          break;
         case 3: /* Add */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 5: *result = ADD_32; return 0;
          }
          break;
         case 7: /* FullSubtract */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 5: *result = FULL_SUBTRACT_32; return 0;
          }
          break;
         case 8: /* Subtract */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 5: *result = SUBTRACT_32; return 0;
          }
          break;
         case 12: /* FullMultiply */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 5: *result = FULL_MULTIPLY_32; return 0;
          }
          break;
         case 13: /* Multiply */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 5: *result = MULTIPLY_32; return 0;
          }
          break;
        }
        break;
       case 3: /* Hash jets chapter */
        code = decodeUptoMaxInt(stream);
        if (code < 0) return code;
        switch (code) {
         case 1: /* SHA-256 section */
          code = decodeUptoMaxInt(stream);
          if (code < 0) return code;
          switch (code) {
           case 1: *result = SHA_256_BLOCK; return 0;
          }
          break;
        }
        break;
      }
      return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;

    } else {
      /* Elements specific jets go here */
      return SIMPLICITY_ERR_DATA_OUT_OF_RANGE;
    }
  }
}

/* Cached copy of each node for all the Elements specific jets.
 * Only to be accessed through 'jetNode'.
 */
static once_flag static_initialized = ONCE_FLAG_INIT;
static dag_node jet_node[] = {
 [ADD_32] =
    { .tag = JET
    , .jet = add_32
    , .sourceIx = word64
    , .targetIx = twoTimesWord32
    },
 [SUBTRACT_32] =
    { .tag = JET
    , .jet = subtract_32
    , .sourceIx = word64
    , .targetIx = twoTimesWord32
    },
 [MULTIPLY_32] =
    { .tag = JET
    , .jet = multiply_32
    , .sourceIx = word64
    , .targetIx = word64
    },
 [FULL_ADD_32] =
    { .tag = JET
    , .jet = full_add_32
    , .sourceIx = twoTimesWord64
    , .targetIx = twoTimesWord32
    },
 [FULL_SUBTRACT_32] =
    { .tag = JET
    , .jet = full_subtract_32
    , .sourceIx = twoTimesWord64
    , .targetIx = twoTimesWord32
    },
 [FULL_MULTIPLY_32] =
    { .tag = JET
    , .jet = full_multiply_32
    , .sourceIx = word128
    , .targetIx = word64
    },
 [SHA_256_BLOCK] =
    { .tag = JET
    , .jet = sha_256_block
    , .sourceIx = word256TimesWord512
    , .targetIx = word256
    },
 [VERSION] =
    { .tag = JET
    , .jet = version
    , .sourceIx = one
    , .targetIx = word32
    },
 [LOCKTIME] =
    { .tag = JET
    , .jet = lockTime
    , .sourceIx = one
    , .targetIx = word32
    },
 [INPUTISPEGIN] =
    { .tag = JET
    , .jet = inputIsPegin
    , .sourceIx = word32
    , .targetIx = sTwo
    },
 [INPUTPREVOUTPOINT] =
    { .tag = JET
    , .jet = inputPrevOutpoint
    , .sourceIx = word32
    , .targetIx = sOutpnt
    },
 [INPUTASSET] =
    { .tag = JET
    , .jet = inputAsset
    , .sourceIx = word32
    , .targetIx = sConfWord256
    },
 [INPUTAMOUNT] =
    { .tag = JET
    , .jet = inputAmount
    , .sourceIx = word32
    , .targetIx = sConfWord64
    },
 [INPUTSCRIPTHASH] =
    { .tag = JET
    , .jet = inputScriptHash
    , .sourceIx = word32
    , .targetIx = sWord256
    },
 [INPUTSEQUENCE] =
    { .tag = JET
    , .jet = inputSequence
    , .sourceIx = word32
    , .targetIx = sWord32
    },
 [INPUTISSUANCEBLINDING] =
    { .tag = JET
    , .jet = inputIssuanceBlinding
    , .sourceIx = word32
    , .targetIx = sSWord256
    },
 [INPUTISSUANCECONTRACT] =
    { .tag = JET
    , .jet = inputIssuanceContract
    , .sourceIx = word32
    , .targetIx = sSWord256
    },
 [INPUTISSUANCEENTROPY] =
    { .tag = JET
    , .jet = inputIssuanceEntropy
    , .sourceIx = word32
    , .targetIx = sSWord256
    },
 [INPUTISSUANCEASSETAMT] =
    { .tag = JET
    , .jet = inputIssuanceAssetAmt
    , .sourceIx = word32
    , .targetIx = sSConfWord64
    },
 [INPUTISSUANCETOKENAMT] =
    { .tag = JET
    , .jet = inputIssuanceTokenAmt
    , .sourceIx = word32
    , .targetIx = sSConfWord64
    },
 [OUTPUTASSET] =
    { .tag = JET
    , .jet = outputAsset
    , .sourceIx = word32
    , .targetIx = sConfWord256
    },
 [OUTPUTAMOUNT] =
    { .tag = JET
    , .jet = outputAmount
    , .sourceIx = word32
    , .targetIx = sConfWord64
    },
 [OUTPUTNONCE] =
    { .tag = JET
    , .jet = outputNonce
    , .sourceIx = word32
    , .targetIx = sSConfWord256
    },
 [OUTPUTSCRIPTHASH] =
    { .tag = JET
    , .jet = outputScriptHash
    , .sourceIx = word32
    , .targetIx = sWord256
    },
 [OUTPUTNULLDATUM] =
    { .tag = JET
    , .jet = outputNullDatum
    , .sourceIx = word64
    , .targetIx = sSWord2TimesWord256PlusTwoPlusWord4
    },
 [SCRIPTCMR] =
    { .tag = JET
    , .jet = scriptCMR
    , .sourceIx = one
    , .targetIx = word256
    },
 [CURRENTINDEX] =
    { .tag = JET
    , .jet = currentIndex
    , .sourceIx = one
    , .targetIx = word32
    },
 [CURRENTISPEGIN] =
    { .tag = JET
    , .jet = currentIsPegin
    , .sourceIx = one
    , .targetIx = two
    },
 [CURRENTPREVOUTPOINT] =
    { .tag = JET
    , .jet = currentPrevOutpoint
    , .sourceIx = one
    , .targetIx = outpnt
    },
 [CURRENTASSET] =
    { .tag = JET
    , .jet = currentAsset
    , .sourceIx = one
    , .targetIx = confWord256
    },
 [CURRENTAMOUNT] =
    { .tag = JET
    , .jet = currentAmount
    , .sourceIx = one
    , .targetIx = confWord64
    },
 [CURRENTSCRIPTHASH] =
    { .tag = JET
    , .jet = currentScriptHash
    , .sourceIx = one
    , .targetIx = word256
    },
 [CURRENTSEQUENCE] =
    { .tag = JET
    , .jet = currentSequence
    , .sourceIx = one
    , .targetIx = word32
    },
 [CURRENTISSUANCEBLINDING] =
    { .tag = JET
    , .jet = currentIssuanceBlinding
    , .sourceIx = one
    , .targetIx = sWord256
    },
 [CURRENTISSUANCECONTRACT] =
    { .tag = JET
    , .jet = currentIssuanceContract
    , .sourceIx = one
    , .targetIx = sWord256
    },
 [CURRENTISSUANCEENTROPY] =
    { .tag = JET
    , .jet = currentIssuanceEntropy
    , .sourceIx = one
    , .targetIx = sWord256
    },
 [CURRENTISSUANCEASSETAMT] =
    { .tag = JET
    , .jet = currentIssuanceAssetAmt
    , .sourceIx = one
    , .targetIx = sConfWord64
    },
 [CURRENTISSUANCETOKENAMT] =
    { .tag = JET
    , .jet = currentIssuanceTokenAmt
    , .sourceIx = one
    , .targetIx = sConfWord64
    },
 [INPUTSHASH] =
    { .tag = JET
    , .jet = inputsHash
    , .sourceIx = one
    , .targetIx = word256
    },
 [OUTPUTSHASH] =
    { .tag = JET
    , .jet = outputsHash
    , .sourceIx = one
    , .targetIx = word256
    },
 [NUMINPUTS] =
    { .tag = JET
    , .jet = numInputs
    , .sourceIx = one
    , .targetIx = word32
    },
 [NUMOUTPUTS] =
    { .tag = JET
    , .jet = numOutputs
    , .sourceIx = one
    , .targetIx = word32
    },
 [FEE] =
    { .tag = JET
    , .jet = NULL /* :TODO: FEE not yet implemented. */
    , .sourceIx = word256
    , .targetIx = word64
    }
 };
static void static_initialize(void) {
  {
    sha256_midstate jet_iv;
    MK_TAG(&jet_iv, JET_TAG);

#define MK_JET(name, h0, h1, h2, h3, h4, h5, h6, h7) \
  do { \
    jet_node[name].cmr = jet_iv; \
    sha256_compression(jet_node[name].cmr.s, (uint32_t[16]){ [8] = h0, h1, h2, h3, h4, h5, h6, h7 }); \
  } while(0)

    /* Jets are identified by their specification's identity Merkle roots. */
    MK_JET(ADD_32,            0xe40466a7u, 0xecf71ce8u, 0x62fb3c15u, 0x4c1e8f84u, 0x5d7e5707u, 0x463a8945u, 0x37a32fc7u, 0x214900adu);
    MK_JET(FULL_ADD_32,       0x4727361eu, 0xa003c1a4u, 0x83e57505u, 0xcf5b405au, 0x8227da1au, 0xddc47e2bu, 0x016c2d09u, 0xbe047fe8u);
    MK_JET(SUBTRACT_32,       0xf76ecad1u, 0xfda50f13u, 0x5bdfe3e5u, 0x33a15009u, 0x8f406261u, 0xc76f6dbfu, 0x6725f1e3u, 0x883c2ae2u);
    MK_JET(FULL_SUBTRACT_32,  0x6d96f68au, 0x945c22e7u, 0x62115c09u, 0x4297b194u, 0xbedc0ce5u, 0xa0c92db6u, 0x4b830a18u, 0xb44df0d0u);
    MK_JET(MULTIPLY_32,       0x161fd03au, 0x92c621b3u, 0x289849ffu, 0x29ad8134u, 0x99d63ed9u, 0x73db0e97u, 0x51785421u, 0xf568d18fu);
    MK_JET(FULL_MULTIPLY_32,  0xaac25361u, 0xe598e354u, 0x38b918b5u, 0x8fd2cef4u, 0xdb3c5d8cu, 0x5e63aa4fu, 0x25e9cec0u, 0xcfd9dfb1u);
    MK_JET(SHA_256_BLOCK,     0xdfc927d3u, 0x9bf7147au, 0x8b0a7f43u, 0x79466870u, 0x824db102u, 0x090a0036u, 0x2923a377u, 0xa91af681u);
#undef MK_JET

  }
  MK_TAG(&jet_node[VERSION].cmr, PRIMITIVE_TAG("version"));
  MK_TAG(&jet_node[LOCKTIME].cmr, PRIMITIVE_TAG("lockTime"));
  MK_TAG(&jet_node[INPUTISPEGIN].cmr, PRIMITIVE_TAG("inputIsPegin"));
  MK_TAG(&jet_node[INPUTPREVOUTPOINT].cmr, PRIMITIVE_TAG("inputPrevOutpoint"));
  MK_TAG(&jet_node[INPUTASSET].cmr, PRIMITIVE_TAG("inputAsset"));
  MK_TAG(&jet_node[INPUTAMOUNT].cmr, PRIMITIVE_TAG("inputAmount"));
  MK_TAG(&jet_node[INPUTSCRIPTHASH].cmr, PRIMITIVE_TAG("inputScriptHash"));
  MK_TAG(&jet_node[INPUTSEQUENCE].cmr, PRIMITIVE_TAG("inputSequence"));
  MK_TAG(&jet_node[INPUTISSUANCEBLINDING].cmr, PRIMITIVE_TAG("inputIssuanceBlinding"));
  MK_TAG(&jet_node[INPUTISSUANCECONTRACT].cmr, PRIMITIVE_TAG("inputIssuanceContract"));
  MK_TAG(&jet_node[INPUTISSUANCEENTROPY].cmr, PRIMITIVE_TAG("inputIssuanceEntropy"));
  MK_TAG(&jet_node[INPUTISSUANCEASSETAMT].cmr, PRIMITIVE_TAG("inputIssuanceAssetAmt"));
  MK_TAG(&jet_node[INPUTISSUANCETOKENAMT].cmr, PRIMITIVE_TAG("inputIssuanceTokenAmt"));
  MK_TAG(&jet_node[OUTPUTASSET].cmr, PRIMITIVE_TAG("outputAsset"));
  MK_TAG(&jet_node[OUTPUTAMOUNT].cmr, PRIMITIVE_TAG("outputAmount"));
  MK_TAG(&jet_node[OUTPUTNONCE].cmr, PRIMITIVE_TAG("outputNonce"));
  MK_TAG(&jet_node[OUTPUTSCRIPTHASH].cmr, PRIMITIVE_TAG("outputScriptHash"));
  MK_TAG(&jet_node[OUTPUTNULLDATUM].cmr, PRIMITIVE_TAG("outputNullDatum"));
  MK_TAG(&jet_node[SCRIPTCMR].cmr, PRIMITIVE_TAG("scriptCMR"));
  MK_TAG(&jet_node[CURRENTINDEX].cmr, PRIMITIVE_TAG("currentIndex"));
  MK_TAG(&jet_node[CURRENTISPEGIN].cmr, PRIMITIVE_TAG("currentIsPegin"));
  MK_TAG(&jet_node[CURRENTPREVOUTPOINT].cmr, PRIMITIVE_TAG("currentPrevOutpoint"));
  MK_TAG(&jet_node[CURRENTASSET].cmr, PRIMITIVE_TAG("currentAsset"));
  MK_TAG(&jet_node[CURRENTAMOUNT].cmr, PRIMITIVE_TAG("currentAmount"));
  MK_TAG(&jet_node[CURRENTSCRIPTHASH].cmr, PRIMITIVE_TAG("currentScriptHash"));
  MK_TAG(&jet_node[CURRENTSEQUENCE].cmr, PRIMITIVE_TAG("currentSequence"));
  MK_TAG(&jet_node[CURRENTISSUANCEBLINDING].cmr, PRIMITIVE_TAG("currentIssuanceBlinding"));
  MK_TAG(&jet_node[CURRENTISSUANCECONTRACT].cmr, PRIMITIVE_TAG("currentIssuanceContract"));
  MK_TAG(&jet_node[CURRENTISSUANCEENTROPY].cmr, PRIMITIVE_TAG("currentIssuanceEntropy"));
  MK_TAG(&jet_node[CURRENTISSUANCEASSETAMT].cmr, PRIMITIVE_TAG("currentIssuanceAssetAmt"));
  MK_TAG(&jet_node[CURRENTISSUANCETOKENAMT].cmr, PRIMITIVE_TAG("currentIssuanceTokenAmt"));
  MK_TAG(&jet_node[INPUTSHASH].cmr, PRIMITIVE_TAG("inputsHash"));
  MK_TAG(&jet_node[OUTPUTSHASH].cmr, PRIMITIVE_TAG("outputsHash"));
  MK_TAG(&jet_node[NUMINPUTS].cmr, PRIMITIVE_TAG("numInputs"));
  MK_TAG(&jet_node[NUMOUTPUTS].cmr, PRIMITIVE_TAG("numOutputs"));
  MK_TAG(&jet_node[FEE].cmr, PRIMITIVE_TAG("fee"));
}

/* Return a copy of the Simplicity node corresponding to the given Elements specific jet 'name'.
 */
static dag_node jetNode(jetName name) {
  call_once(&static_initialized, &static_initialize);

  return jet_node[name];
}

/* Decode an Elements specific jet from 'stream' into 'node'.
 * All jets begin with a bit prefix of '1' which needs to have already been consumed from the 'stream'.
 * Returns 'SIMPLICITY_ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'SIMPLICITY_ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'SIMPLICITY_ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'dag' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != node
 *               NULL != stream
 */
int32_t decodeJet(dag_node* node, bitstream* stream) {
  jetName name;
  int32_t err = decodePrimitive(&name, stream);
  if (err < 0) return err;
  *node = jetNode(name);
  return 0;
}
