#include "type.h"

#include <assert.h>
#include <stdbool.h>

#include "bounded.h"

/* Prepends the Simplicity TMR tag prefix to a string literal 's'. */
#define TYPE_TAG(s) "Simplicity\x1F" "Type\x1F" s

/* Given a the 'kind' of a Simplicity type, return the SHA-256 hash of its associated TMR tag.
 * This is the "initial value" for computing the type Merkle root for that type.
 */
static sha256_midstate tmrIV(typeName kind) {
  /* Cache the initial values for all the 'typeName's. */
  static bool static_initialized = false;
  static sha256_midstate unitIV,
                         sumIV,
                         prodIV;
  if (!static_initialized) {
    MK_TAG(unitIV.s, TYPE_TAG("unit"));
    MK_TAG(sumIV.s, TYPE_TAG("sum"));
    MK_TAG(prodIV.s, TYPE_TAG("prod"));
    static_initialized = true;
  }

  switch (kind) {
   case ONE: return unitIV;
   case SUM: return sumIV;
   case PRODUCT: return prodIV;
  }
  /* Impossible to reach here (unless you call with uninitialized values). */
  assert(false);
  return (sha256_midstate){0};
}

/* Given a well-formed 'type_dag', compute the bitSizes and type Merkle roots of all subexpressions.
 * For all 'i', 0 <= 'i' < 'len',
 *   'type_dag[i].typeMerkleRoot' will be the TMR
 *   and 'type_dag[i].bitSize' will be the bitSize of the subexpression denoted by the slice
 *
 *     (type_dag[i + 1])type_dag.
 *
 * Precondition: type type_dag[len] and 'type_dag' is well-formed.
 */
void computeTypeAnalyses(type* type_dag, const size_t len) {
  for (size_t i = 0; i < len; ++i) {
    switch (type_dag[i].kind) {
     case ONE:
      type_dag[i].bitSize = 0;
      break;
     case SUM:
      type_dag[i].bitSize = max(type_dag[type_dag[i].typeArg[0]].bitSize, type_dag[type_dag[i].typeArg[1]].bitSize);
      bounded_inc(&type_dag[i].bitSize);
      break;
     case PRODUCT:
      type_dag[i].bitSize = bounded_add(type_dag[type_dag[i].typeArg[0]].bitSize, type_dag[type_dag[i].typeArg[1]].bitSize);
    }

    type_dag[i].typeMerkleRoot = tmrIV(type_dag[i].kind);

    uint32_t block[16];
    switch (type_dag[i].kind) {
     case ONE: break;
     case SUM:
     case PRODUCT:
      memcpy(block, type_dag[type_dag[i].typeArg[0]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      memcpy(block + 8, type_dag[type_dag[i].typeArg[1]].typeMerkleRoot.s, sizeof(uint32_t[8]));
      sha256_compression(type_dag[i].typeMerkleRoot.s, block);
    }
  }
}
