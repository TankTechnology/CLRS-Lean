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
  threshold from Mathlib's Ackermann function, and instantiates the
  CLRS/Alstrup rank-level-index potential.  Its nested modules count the actual
  Batteries parent recursion, prove a conserved root-mass invariant for every
  reachable state, establish the local find/link/union amortized inequalities,
  and derive the whole-run bound `9 * (m + n) * alpha(n)`.  Under the standard
  `n <= m` assumption, the supplied corollary is `18 * m * alpha(n)`.
- The nested Section 23.2 bridge turns a connectivity-faithful union-find state
  family into the existing verified Kruskal cycle-test interface.

## Closure Boundary

Chapter 21's advertised functional-correctness and inverse-Ackermann
amortization stack is complete for the explicit cost model.  The intermediate
`O(m log n)` theorem remains useful as a simpler sanity bound.  Lower-level
array-write/RAM constants and Chapter 23's incremental stateful Kruskal scan
are separate implementation refinements, not missing Chapter 21 core groups.
