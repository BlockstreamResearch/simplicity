/* This module implements the 'primitive.h' interface for the Elements application of Simplicity.
 */
#include "primitive.h"

#include "jets.h"
#include "../../tag.h"
#include "../../unreachable.h"

#define PRIMITIVE_TAG(s) "Simplicity\x1F" "Primitive\x1F" "Elements\x1F" s

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
      },
   [LOCKTIME] =
      { .tag = JET
      , .jet = lockTime
      },
   [INPUTISPEGIN] =
      { .tag = JET
      , .jet = inputIsPegin
      },
   [INPUTPREVOUTPOINT] =
      { .tag = JET
      , .jet = inputPrevOutpoint
      },
   [INPUTASSET] =
      { .tag = JET
      , .jet = inputAsset
      },
   [INPUTAMOUNT] =
      { .tag = JET
      , .jet = inputAmount
      },
   [INPUTSCRIPTHASH] =
      { .tag = JET
      , .jet = inputScriptHash
      },
   [INPUTSEQUENCE] =
      { .tag = JET
      , .jet = inputSequence
      },
   [INPUTISSUANCEBLINDING] =
      { .tag = JET
      , .jet = inputIssuanceBlinding
      },
   [INPUTISSUANCECONTRACT] =
      { .tag = JET
      , .jet = inputIssuanceContract
      },
   [INPUTISSUANCEENTROPY] =
      { .tag = JET
      , .jet = inputIssuanceEntropy
      },
   [INPUTISSUANCEASSETAMT] =
      { .tag = JET
      , .jet = inputIssuanceAssetAmt
      },
   [INPUTISSUANCETOKENAMT] =
      { .tag = JET
      , .jet = inputIssuanceTokenAmt
      },
   [OUTPUTASSET] =
      { .tag = JET
      , .jet = outputAsset
      },
   [OUTPUTAMOUNT] =
      { .tag = JET
      , .jet = outputAmount
      },
   [OUTPUTNONCE] =
      { .tag = JET
      , .jet = outputNonce
      },
   [OUTPUTSCRIPTHASH] =
      { .tag = JET
      , .jet = outputScriptHash
      },
   [OUTPUTNULLDATUM] =
      { .tag = JET
      , .jet = outputNullDatum
      },
   [SCRIPTCMR] =
      { .tag = JET
      , .jet = scriptCMR
      },
   [CURRENTINDEX] =
      { .tag = JET
      , .jet = currentIndex
      },
   [CURRENTISPEGIN] =
      { .tag = JET
      , .jet = currentIsPegin
      },
   [CURRENTPREVOUTPOINT] =
      { .tag = JET
      , .jet = currentPrevOutpoint
      },
   [CURRENTASSET] =
      { .tag = JET
      , .jet = currentAsset
      },
   [CURRENTAMOUNT] =
      { .tag = JET
      , .jet = currentAmount
      },
   [CURRENTSCRIPTHASH] =
      { .tag = JET
      , .jet = currentScriptHash
      },
   [CURRENTSEQUENCE] =
      { .tag = JET
      , .jet = currentSequence
      },
   [CURRENTISSUANCEBLINDING] =
      { .tag = JET
      , .jet = currentIssuanceBlinding
      },
   [CURRENTISSUANCECONTRACT] =
      { .tag = JET
      , .jet = currentIssuanceContract
      },
   [CURRENTISSUANCEENTROPY] =
      { .tag = JET
      , .jet = currentIssuanceEntropy
      },
   [CURRENTISSUANCEASSETAMT] =
      { .tag = JET
      , .jet = currentIssuanceAssetAmt
      },
   [CURRENTISSUANCETOKENAMT] =
      { .tag = JET
      , .jet = currentIssuanceTokenAmt
      },
   [INPUTSHASH] =
      { .tag = JET
      , .jet = inputsHash
      },
   [OUTPUTSHASH] =
      { .tag = JET
      , .jet = outputsHash
      },
   [NUMINPUTS] =
      { .tag = JET
      , .jet = numInputs
      },
   [NUMOUTPUTS] =
      { .tag = JET
      , .jet = numOutputs
      },
   [FEE] =
      { .tag = JET
      , .jet = NULL /* :TODO: FEE not yet implemented. */
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
