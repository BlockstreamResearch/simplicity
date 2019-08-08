/* This module implements the 'primitive.h' interface for the Elements application of Simplicity.
 */
#include "primitive.h"

#include "jets.h"
#include "../../tag.h"
#include "../../unreachable.h"

#define PRIMITIVE_TAG(s) "Simplicity\x1F" "Primitive\x1F" "Elements\x1F" s

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
  twoPlusWord4,
  pubKeyPlusBitPlusWord4,
  sPubKeyPlusBitPlusWord4,
  sSPubKeyPlusBitPlusWord4,
  NumberOfTypeNames
};

/* Allocate a fresh set of unification variables bound to at least all the types necessary
 * for all the jets that can be created by 'decodeJet', and also the type 'TWO^256'.
 * Return the number of non-trivial bindings created.
 *
 * However, if malloc fails, then return 0.
 *
 * Precondition: NULL != bound_var;
 *               NULL != word256_ix;
 *
 * Postcondition: Either '*bound_var == NULL' and the function returns 0
 *                or 'unification_var (*bound_var)[N]' is an array of fresh unification variables bound to various types
 *                   such that for any 'jet : A |- B' there is some 'i < N' and 'j < N' such that '(*bound_var)[i]' is bound to 'A'
 *                                                                                            and '(*bound_var)[j]' is bound to 'B'
 *                   and, in particular, '*word256_ix < N' and '(*bound_var)[*word256_ix]' is bound the type 'TWO^256'
 */
size_t mallocBoundVars(unification_var** bound_var, size_t* word256_ix) {
  *bound_var = malloc(sizeof(unification_var[NumberOfTypeNames]));
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
  (*bound_var)[twoPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[two], &(*bound_var)[word4] } } };
  (*bound_var)[pubKeyPlusBitPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[pubkey], &(*bound_var)[twoPlusWord4] } } };
  (*bound_var)[sPubKeyPlusBitPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[pubKeyPlusBitPlusWord4] } } };
  (*bound_var)[sSPubKeyPlusBitPlusWord4] = (unification_var){ .isBound = true,
      .bound = { .kind = SUM,     .arg = { &(*bound_var)[one], &(*bound_var)[sPubKeyPlusBitPlusWord4] } } };

  *word256_ix = word256;

  /* 'one' is a trivial binding, so we made 'NumberOfTypeNames - 1' non-trivial bindings. */
  return NumberOfTypeNames - 1;
};

/* An enumeration of the names of Elements specific jets and primitives. */
typedef enum jetName
{ VERSION
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
 * All application specific jets begin with a bit prefix of '10' which needs to have already been consumed from the 'stream'.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
 * In the above error cases, 'result' may be modified.
 * Returns 0 if successful.
 *
 * Precondition: NULL != result
 *               NULL != stream
 */
static int32_t decodePrimitive(jetName* result, bitstream* stream) {
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
    *result = FEE; return ERR_DATA_OUT_OF_RANGE;
  }
  assert(false);
  UNREACHABLE;
}

/* Return a copy of the Simplicity node corresponding to the given Elements specific jet 'name'.
 */
static dag_node jetNode(jetName name) {
  /* Cache a copy of each node for all the Elements specific jets. */
  static bool static_initialized = false;
  static dag_node node[] = {
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
      , .targetIx = sSPubKeyPlusBitPlusWord4
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

  if (!static_initialized) {
    MK_TAG(node[VERSION].wmr.s, PRIMITIVE_TAG("version"));
    MK_TAG(node[LOCKTIME].wmr.s, PRIMITIVE_TAG("lockTime"));
    MK_TAG(node[INPUTISPEGIN].wmr.s, PRIMITIVE_TAG("inputIsPegin"));
    MK_TAG(node[INPUTPREVOUTPOINT].wmr.s, PRIMITIVE_TAG("inputPrevOutpoint"));
    MK_TAG(node[INPUTASSET].wmr.s, PRIMITIVE_TAG("inputAsset"));
    MK_TAG(node[INPUTAMOUNT].wmr.s, PRIMITIVE_TAG("inputAmount"));
    MK_TAG(node[INPUTSCRIPTHASH].wmr.s, PRIMITIVE_TAG("inputScriptHash"));
    MK_TAG(node[INPUTSEQUENCE].wmr.s, PRIMITIVE_TAG("inputSequence"));
    MK_TAG(node[INPUTISSUANCEBLINDING].wmr.s, PRIMITIVE_TAG("inputIssuanceBlinding"));
    MK_TAG(node[INPUTISSUANCECONTRACT].wmr.s, PRIMITIVE_TAG("inputIssuanceContract"));
    MK_TAG(node[INPUTISSUANCEENTROPY].wmr.s, PRIMITIVE_TAG("inputIssuanceEntropy"));
    MK_TAG(node[INPUTISSUANCEASSETAMT].wmr.s, PRIMITIVE_TAG("inputIssuanceAssetAmt"));
    MK_TAG(node[INPUTISSUANCETOKENAMT].wmr.s, PRIMITIVE_TAG("inputIssuanceTokenAmt"));
    MK_TAG(node[OUTPUTASSET].wmr.s, PRIMITIVE_TAG("outputAsset"));
    MK_TAG(node[OUTPUTAMOUNT].wmr.s, PRIMITIVE_TAG("outputAmount"));
    MK_TAG(node[OUTPUTNONCE].wmr.s, PRIMITIVE_TAG("outputNonce"));
    MK_TAG(node[OUTPUTSCRIPTHASH].wmr.s, PRIMITIVE_TAG("outputScriptHash"));
    MK_TAG(node[OUTPUTNULLDATUM].wmr.s, PRIMITIVE_TAG("outputNullDatum"));
    MK_TAG(node[SCRIPTCMR].wmr.s, PRIMITIVE_TAG("scriptCMR"));
    MK_TAG(node[CURRENTINDEX].wmr.s, PRIMITIVE_TAG("currentIndex"));
    MK_TAG(node[CURRENTISPEGIN].wmr.s, PRIMITIVE_TAG("currentIsPegin"));
    MK_TAG(node[CURRENTPREVOUTPOINT].wmr.s, PRIMITIVE_TAG("currentPrevOutpoint"));
    MK_TAG(node[CURRENTASSET].wmr.s, PRIMITIVE_TAG("currentAsset"));
    MK_TAG(node[CURRENTAMOUNT].wmr.s, PRIMITIVE_TAG("currentAmount"));
    MK_TAG(node[CURRENTSCRIPTHASH].wmr.s, PRIMITIVE_TAG("currentScriptHash"));
    MK_TAG(node[CURRENTSEQUENCE].wmr.s, PRIMITIVE_TAG("currentSequence"));
    MK_TAG(node[CURRENTISSUANCEBLINDING].wmr.s, PRIMITIVE_TAG("currentIssuanceBlinding"));
    MK_TAG(node[CURRENTISSUANCECONTRACT].wmr.s, PRIMITIVE_TAG("currentIssuanceContract"));
    MK_TAG(node[CURRENTISSUANCEENTROPY].wmr.s, PRIMITIVE_TAG("currentIssuanceEntropy"));
    MK_TAG(node[CURRENTISSUANCEASSETAMT].wmr.s, PRIMITIVE_TAG("currentIssuanceAssetAmt"));
    MK_TAG(node[CURRENTISSUANCETOKENAMT].wmr.s, PRIMITIVE_TAG("currentIssuanceTokenAmt"));
    MK_TAG(node[INPUTSHASH].wmr.s, PRIMITIVE_TAG("inputsHash"));
    MK_TAG(node[OUTPUTSHASH].wmr.s, PRIMITIVE_TAG("outputsHash"));
    MK_TAG(node[NUMINPUTS].wmr.s, PRIMITIVE_TAG("numInputs"));
    MK_TAG(node[NUMOUTPUTS].wmr.s, PRIMITIVE_TAG("numOutputs"));
    MK_TAG(node[FEE].wmr.s, PRIMITIVE_TAG("fee"));
    static_initialized = true;
  }

  return node[name];
}

/* Decode an Elements specific jet from 'stream' into 'node'.
 * All application specific jets begin with a bit prefix of '10' which needs to have already been consumed from the 'stream'.
 * Returns 'ERR_DATA_OUT_OF_RANGE' if the stream's prefix doesn't match any valid code for a jet.
 * Returns 'ERR_BITSTRING_EOF' if not enough bits are available in the 'stream'.
 * Returns 'ERR_BITSTREAM_ERROR' if an I/O error occurs when reading from the 'stream'.
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
