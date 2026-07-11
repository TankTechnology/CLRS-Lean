# Chapter 21 Closure Audit - 2026-07-10

## Scope

This audit seals the represented Chapter 21 model: abstract disjoint-set
semantics, weighted linked-list analysis, executable Batteries union-find
correctness, and union-by-rank with path-compression amortization.

## Closed Proof Chains

- Sections 21.1-21.3 refine all represented operations to one partition model.
- `CostedExecution` counts the real Batteries parent recursion, preserves a
  reachable rank-mass budget, and proves the intermediate `O(m log n)` bound.
- `InverseAckermann` defines Ackermann levels, indices, and node potential;
  proves path compression cannot increase potential; and bounds link growth by
  two units.
- Traversed find nodes split into released, Ackermann-boundary, and top-level
  unpleasant classes.  The last two classes each inject into a set of size at
  most `alpha(root)`.
- `costedFind_amortized_le` and `costedUnion_amortized_le` discharge the local
  amortized obligations for the actual Batteries implementation.
- `run_cost_le_inverseAckermann` proves
  `cost <= 9 * (m + n) * alpha(n)`; its standard `n <= m` corollary proves
  `cost <= 18 * m * alpha(n)`.

## Verification Boundary

The public interface is protected by `Tests/Chapter_21_Interface.lean`.  The
chapter has no `sorry`, `admit`, or added axioms.  Lower-level array-write/RAM
constants remain a future implementation refinement.  Chapter 23 now consumes
this costed state machine in its incremental Kruskal scan without reopening
the Chapter 21 theorem boundary.
