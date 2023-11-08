#include "dag.h"

const size_t c_sizeof_dag_node = sizeof(dag_node);

void c_dag_node_get_cmr(unsigned char *cmr, const dag_node* node) {
  sha256_fromMidstate(cmr, node->cmr.s);
}
