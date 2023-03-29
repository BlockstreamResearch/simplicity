# Analysis of dag based memory use.

This section focuses on allocations Simplicity program dag size.
This is independent from the analysis of memory use based on transaction size in Elements.

We only analyze the "good" path where execution is successful which is the worst case from an allocation point of view.

## Starting from execSimplicity.

1. Allocate with `decodeMallocDag`
1. Allocate with `mallocTypeInference`.
1. Allocate `imr_buf`.
1. Allocate within `verifyNoDuplicateIdentityRoots`.
1. Free `imr_buf`.
1. AMR analysis goes here, but it is only used for testing, and we exclude it from our analysis.
1. Allocate within `evalTCOProgram`.
1. Free allocation from `mallocTypeInference` and from `decodeMallocDag`.

### `decodeMallocDag`

1. Allocate and return `dag_node[dagLen]`.

`sizeof(dag_node) = 96`.
This results in a net use of 96 bytes per DAG node.

### `mallocTypeInference`

1. Allocate `arrow`.
1. Allocate with `mallocBoundVars`.
1. Allocate `type_dag`.
1. Free `arrow` and allocation from `mallocBoundVars`.
1. Return the `type_dag` allocation.

The `arrow` allocation consists of a pair of `unification_var`s per `dagLen`.
`sizeof(unification_var) = 56`.
This brings our total allocation to 96+2×56 = 208 bytes per DAG node.

The `mallocBoundVars` allocates an additional `max_extra_vars(census)` plus a constant number `unification_var`s.
The constant number is based on the types of jets and is independent of `dagLen`.
`max_extra_vars(census)` is at most `4 * dagLen`.
This brings our total allocation to at most 208+4×56 = 432 bytes per DAG node (excluding an additional constant amount of allocation).

The `type_dag` allocation is `type[1 + bindings_used]`.
`sizeof(type) = 72`.
The value of `bindings_used` is at most `4 * dagLen` plus a constant.
This brings our total allocation to at most 432 + 4×72 = 720 bytes per DAG node (excluding an additional constant amount of allocation).

After two of the allocations are freed, our allocation is reduced to 96+4×72 = 384 bytes per DAG node.

### Allocation of `imr_buf`

The `imr_buf` allocation is `sha256_midstate[dagLen]`.
`sizeof(sha256_midstate) = 32`.
This brings our total allocation to at most 384 + 32 = 416 bytes per DAG node.

### `verifyNoDuplicateIdentityRoots`

This function calls `hasDuplicates` which allocates `(sha256_midsate*)[dagLen]`
`sizeof(sha256_midstate*) = 8`.
This brings our total allocation to at most 416 + 8 = 424 bytes per DAG node.

This allocation is then freed bringing our total allocation back down to 416 bytes per DAG node.

Note that `hasDuplicates` also allocates and frees a `size_t[8448]` array independent of `dagLen`.

### Freeing of `imr_buf`

This brings our total allocation back down to 384 bytes per DAG node.

### `evalTCOProgram`

1. Allocation within `computeEvalTCOBound`.
1. Allocate `cells`.
1. Allocate `frames`.
1. Allocate `stack`.
1. Free `cells`, `frames`, and `stack`.

`computeEvalTCOBound` allocates `memBound[dagLen]` and then frees it.
`sizeof(memBound) = 6*sizeof(size_t) = 48`.
This temporarily increases our total allocation to 384 + 48 = 432 bytes per DAG node before returning it back to 384 bytes per DAG node.

The `cells` allocation is `UWORD[UWORDBound]`.
`sizeof(UWORD) = 8`.
The `UWORDBound` value is not linear in the size of the DAG, but is bound by the consensus parameter of `cellsBound`, which is 5 Mebi.
The total size of `cells` is at most 40 Mebibytes.

The `frames` allocation is `frameItem[stackBound]`.
`sizeof(frameItem) = 16` and `stackBound` is at most `2*dagLen`.

The `stack` allocation is `call[dagLen]`.
`sizeof(call) = 2*sizeof(size_t) = 16`.

All together this increases our total allocation to at most 384 + 2×16 + 16 = 432 bytes per dagLen plus the size of the `cells` allocation, before returning it back to 384 bytes per DAG node.

### Free of allocations from `mallocTypeInference` and from `decodeMallocDag`

After these allocations are freed there is no remaining allocated memory from Simplicity execution.

## Results

This analysis give a peek heap usage of 720 bytes per DAG node that occurs during type inferrence.
Due to block size limitations, there are at most 2^23 DAG nodes per block (likely closer to 2^22) which caps the worst case heap amount used at 5760 MiB (plus a constant).  A more careful analysis is likely to halve that value.
