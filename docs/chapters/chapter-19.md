# Chapter 19 - Fibonacci Heaps

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_19.lean`
- Interface test: `Tests/Chapter_19_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter19.FibHeap.makeHeap_correct`
- `CLRS.Chapter19.FibHeap.potential_makeHeap`
- `CLRS.Chapter19.FibHeap.potential_nonneg`
- `CLRS.Chapter19.FibHeap.minimum_correct`
- `CLRS.Chapter19.FibHeap.minimum_none_iff`
- `CLRS.Chapter19.FibHeap.insert_correct`
- `CLRS.Chapter19.FibHeap.insert_mem_iff`
- `CLRS.Chapter19.FibHeap.union_correct`
- `CLRS.Chapter19.FibHeap.union_mem_iff`
- `CLRS.Chapter19.FibHeap.extractMin_correct`
- `CLRS.Chapter19.FibHeap.extractMin_mem_iff`
- `CLRS.Chapter19.FibHeap.extractMin_none_iff`
- `CLRS.Chapter19.FibHeap.decreaseKey_correct`
- `CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`
- `CLRS.Chapter19.FibHeap.delete_correct`
- `CLRS.Chapter19.FibHeap.delete_mem_iff`
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

## Remaining Work

The current chapter is an abstract finite-key-set specification with the
standard heap potential's zero-initial, nonnegative, and telescoping facts.  It
also includes the first power-of-two lower-bound bridge for the Fibonacci-style
degree sequence, including the half-index form used by later logarithmic-degree
arguments and a conditional natural binary-log bridge from a Fibonacci-style
subtree-size lower bound to a degree budget.  The chapter still defers pointer
handles, heap-ordered
forests, cascading cuts, consolidation
arrays, duplicate keys, and the subtree-size induction leading to the true
Fibonacci logarithmic degree theorem.
