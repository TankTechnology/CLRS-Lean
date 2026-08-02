# Chapter 19 - Fibonacci Heaps

- Status: `main-proof-complete-for-correctness`
- Lean entry: `CLRSLean/Chapter_19.lean`
- Interface test: `Tests/Chapter_19_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter19.FibHeap.makeHeap_correct`
- `CLRS.Chapter19.FibHeap.makeHeap_valid`
- `CLRS.Chapter19.FibHeap.makeHeap_minimum_none`
- `CLRS.Chapter19.FibHeap.potential_makeHeap`
- `CLRS.Chapter19.FibHeap.potential_nonneg`
- `CLRS.Chapter19.FibHeap.minimum_correct`
- `CLRS.Chapter19.FibHeap.minimum_mem`
- `CLRS.Chapter19.FibHeap.minimum_le`
- `CLRS.Chapter19.FibHeap.minimum_none_iff`
- `CLRS.Chapter19.FibHeap.minimum_none_of_empty`
- `CLRS.Chapter19.FibHeap.minimum_ne_none_of_nonempty`
- `CLRS.Chapter19.FibHeap.insert_correct`
- `CLRS.Chapter19.FibHeap.insert_valid`
- `CLRS.Chapter19.FibHeap.insert_mem_iff`
- `CLRS.Chapter19.FibHeap.insert_mem_self`
- `CLRS.Chapter19.FibHeap.insert_mem_old`
- `CLRS.Chapter19.FibHeap.insert_not_mem_iff`
- `CLRS.Chapter19.FibHeap.insert_not_mem_of_ne`
- `CLRS.Chapter19.FibHeap.insert_minimum_correct`
- `CLRS.Chapter19.FibHeap.insert_minimum_mem`
- `CLRS.Chapter19.FibHeap.insert_minimum_le_inserted`
- `CLRS.Chapter19.FibHeap.insert_minimum_le_old`
- `CLRS.Chapter19.FibHeap.insert_minimum_none_iff`
- `CLRS.Chapter19.FibHeap.insert_minimum_ne_none`
- `CLRS.Chapter19.FibHeap.union_correct`
- `CLRS.Chapter19.FibHeap.union_valid`
- `CLRS.Chapter19.FibHeap.union_mem_iff`
- `CLRS.Chapter19.FibHeap.union_mem_left`
- `CLRS.Chapter19.FibHeap.union_mem_right`
- `CLRS.Chapter19.FibHeap.union_not_mem_iff`
- `CLRS.Chapter19.FibHeap.union_not_mem_of_not_mem`
- `CLRS.Chapter19.FibHeap.union_minimum_correct`
- `CLRS.Chapter19.FibHeap.union_minimum_mem`
- `CLRS.Chapter19.FibHeap.union_minimum_le_left`
- `CLRS.Chapter19.FibHeap.union_minimum_le_right`
- `CLRS.Chapter19.FibHeap.union_minimum_none_iff`
- `CLRS.Chapter19.FibHeap.union_minimum_none_of_empty`
- `CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_left`
- `CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_right`
- `CLRS.Chapter19.FibHeap.extractMin_correct`
- `CLRS.Chapter19.FibHeap.extractMin_valid`
- `CLRS.Chapter19.FibHeap.extractMin_mem_iff`
- `CLRS.Chapter19.FibHeap.extractMin_not_mem`
- `CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`
- `CLRS.Chapter19.FibHeap.extractMin_not_mem_iff`
- `CLRS.Chapter19.FibHeap.extractMin_not_mem_old`
- `CLRS.Chapter19.FibHeap.extractMin_none_iff`
- `CLRS.Chapter19.FibHeap.extractMin_none_of_empty`
- `CLRS.Chapter19.FibHeap.extractMin_ne_none_of_nonempty`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_mem`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_le_old`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_of_all_eq`
- `CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne_none_of_remaining`
- `CLRS.Chapter19.FibHeap.decreaseKey_correct`
- `CLRS.Chapter19.FibHeap.decreaseKey_valid`
- `CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`
- `CLRS.Chapter19.FibHeap.decreaseKey_mem_new`
- `CLRS.Chapter19.FibHeap.decreaseKey_mem_old`
- `CLRS.Chapter19.FibHeap.decreaseKey_oldKey_mem_iff`
- `CLRS.Chapter19.FibHeap.decreaseKey_oldKey_not_mem_of_ne`
- `CLRS.Chapter19.FibHeap.decreaseKey_not_mem_iff`
- `CLRS.Chapter19.FibHeap.decreaseKey_not_mem_of_ne`
- `CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`
- `CLRS.Chapter19.FibHeap.decreaseKey_minimum_mem`
- `CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_new`
- `CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_old`
- `CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`
- `CLRS.Chapter19.FibHeap.decreaseKey_minimum_ne_none`
- `CLRS.Chapter19.FibHeap.delete_correct`
- `CLRS.Chapter19.FibHeap.delete_valid`
- `CLRS.Chapter19.FibHeap.delete_mem_iff`
- `CLRS.Chapter19.FibHeap.delete_not_mem`
- `CLRS.Chapter19.FibHeap.delete_mem_of_ne`
- `CLRS.Chapter19.FibHeap.delete_not_mem_iff`
- `CLRS.Chapter19.FibHeap.delete_not_mem_old`
- `CLRS.Chapter19.FibHeap.delete_not_mem_of_eq`
- `CLRS.Chapter19.FibHeap.delete_minimum_correct`
- `CLRS.Chapter19.FibHeap.delete_minimum_ne`
- `CLRS.Chapter19.FibHeap.delete_minimum_mem`
- `CLRS.Chapter19.FibHeap.delete_minimum_le_old`
- `CLRS.Chapter19.FibHeap.delete_minimum_none_iff`
- `CLRS.Chapter19.FibHeap.delete_minimum_none_of_all_eq`
- `CLRS.Chapter19.FibHeap.delete_minimum_ne_none_of_remaining`
- `CLRS.Chapter19.FibHeap.heapPotential_telescope`
- `CLRS.Chapter19.FibHeap.fibLowerBound_step`
- `CLRS.Chapter19.FibHeap.fibLowerBound_pos`
- `CLRS.Chapter19.FibHeap.fibLowerBound_le_succ`
- `CLRS.Chapter19.FibHeap.fibLowerBound_monotone`
- `CLRS.Chapter19.FibHeap.fibLowerBound_add_two_ge_double`
- `CLRS.Chapter19.FibHeap.fibLowerBound_even_lower_bound`
- `CLRS.Chapter19.FibHeap.fibLowerBound_half_lower_bound`
- `CLRS.Chapter19.FibHeap.degreeIndex_half_le_log_card`
- `CLRS.Chapter19.FibHeap.degreeIndex_le_twice_log_card_add_one`
- `CLRS.Chapter19.FibHeap.degree_bound_log`

## Section 19.4 Structural Degree Surface

- `CLRS.Chapter19.FTree.Wellformed`
- `CLRS.Chapter19.FTree.wellformed_size_ge_fibLowerBound`
- `CLRS.Chapter19.FTree.goldenRatio_pow_le_fibLowerBound`
- `CLRS.Chapter19.FTree.wellformed_goldenRatio_pow_le_size`
- `CLRS.Chapter19.FTree.wellformed_degree_le_logb`
- `CLRS.Chapter19.FTree.wellformed_degree_le_floor_logb`
- `CLRS.Chapter19.FTree.wellformed_degree_le_twice_log_two`
- `CLRS.Chapter19.FTree.wellformed_append_child`
- `CLRS.Chapter19.FTree.link_wellformed`
- `CLRS.Chapter19.FTree.minTree`
- `CLRS.Chapter19.FTree.minTree_size`
- `CLRS.Chapter19.FTree.minTree_wellformed`
- `CLRS.Chapter19.FTree.exists_wellformed_size_eq_fibLowerBound`

## Executable Core and Amortized Analysis

The persistent `FHNode`/`FH` layer now completes the represented Chapter 19
algorithm stack: exact duplicate-preserving key bags, a cached minimum,
degree-bucket `LINK`/`CONSOLIDATE`, executable extract-min, duplicate-safe
occurrence paths and zippers, arbitrary-node CUT and CASCADING-CUT, executable
decrease-key and delete, and preservation of `FH.Valid` throughout.  Its
standard `t(H) + 2m(H)` potential proves:

- constant amortized cost for handle-directed decrease-key;
- logarithmic amortized cost for extract-min and delete;
- exact erasure from costed operations to the structural algorithms; and
- an exact operation-trace telescope bounded by the sum of the certified
  per-operation budgets.

Mutable circular doubly linked lists, allocation, and a concrete RAM/pointer
latency refinement remain optional implementation layers; they are not missing
core correctness groups for the persistent executable model.
