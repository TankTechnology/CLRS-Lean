# Chapter 21: Data Structures for Disjoint Sets

The represented chapter is organized around one common partition semantics.
Both executable representations prove refinement to that specification.

## Proved Boundary

- Section 21.1 defines equivalence-class partitions, exact union semantics, and
  monotonic operation traces.
- Section 21.2 models the linked-list head/size tables, proves weighted-union
  correctness and representative preservation, and derives the `n log n`
  pointer-rewrite bound from per-element size doubling.
- Section 21.3 reuses `Batteries.Data.UnionFind` and proves singleton creation,
  path-compressing find, union by rank, and Boolean equivalence checking against
  the partition specification.
- Section 21.4 proves parent-rank/path bounds, defines an inverse-Ackermann
  threshold from Mathlib's Ackermann function, and packages the potential-
  method aggregate theorem.  Its nested costed-execution module counts the
  actual Batteries parent recursion, proves a conserved root-mass invariant
  for every reachable state, erases exactly to the Batteries operations, and
  derives a whole-run `m * (2 * log2 n + 3)` bound.
- The nested Section 23.2 bridge turns a connectivity-faithful union-find state
  family into the existing verified Kruskal cycle-test interface.

## Remaining Refinement

The concrete step-counting semantics and logarithmic intermediate theorem are
now present.  The exact low-level `O(m alpha(n))` claim still requires an
Ackermann-level potential assignment proving that each concrete parent
traversal has bounded amortized charge.  The Kruskal bridge is currently
extensional in the selected edge set; an incremental stateful scan is the
corresponding implementation target.
