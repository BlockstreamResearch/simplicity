#include "dag.h"
#include "bitstream.h"
#include "bitstring.h"

const size_t c_sizeof_dag_node = sizeof(dag_node);

void c_compute_word_cmr(unsigned char *cmr, bitstream* stream, size_t offset, size_t n) {
  sha256_midstate result;
  bitstring value;
  readBitstring(&value, offset, stream); /* skip offset many bits. */
  readBitstring(&value, (size_t)1 << n, stream);
  result = computeWordCMR(&value, n);
  sha256_fromMidstate(cmr, result.s);
}

void c_dag_node_get_cmr(unsigned char *cmr, const dag_node* node) {
  sha256_fromMidstate(cmr, node->cmr.s);
}
