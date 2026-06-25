# Chapter 19 - Fibonacci Heaps

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_19.lean`
- Interface test: `Tests/Chapter_19_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter19.FibHeap.makeHeap_correct`
- `CLRS.Chapter19.FibHeap.minimum_correct`
- `CLRS.Chapter19.FibHeap.insert_correct`
- `CLRS.Chapter19.FibHeap.union_correct`
- `CLRS.Chapter19.FibHeap.extractMin_correct`
- `CLRS.Chapter19.FibHeap.decreaseKey_correct`
- `CLRS.Chapter19.FibHeap.delete_correct`
- `CLRS.Chapter19.FibHeap.heapPotential_telescope`
- `CLRS.Chapter19.FibHeap.fibLowerBound_step`
- `CLRS.Chapter19.FibHeap.degree_bound_log`

## Remaining Work

The current chapter is an abstract finite-key-set specification.  It defers
pointer handles, heap-ordered forests, cascading cuts, consolidation arrays,
duplicate keys, and the subtree-size induction leading to the true Fibonacci
logarithmic degree theorem.
