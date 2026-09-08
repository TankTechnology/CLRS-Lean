# Chapters 4–6 Repair Record

Issues [#348](https://github.com/TankTechnology/CLRS-Lean/issues/348) through
[#350](https://github.com/TankTechnology/CLRS-Lean/issues/350) were resolved.

- **Chapter 4:** `MatrixExecution` returns matrix results and operation counts for
  scalar leaves, eight-multiplication recursion, and Strassen recursion. Erasure
  recovers the original algorithms. The actual `2^k` executions now support the
  stated cubic and `n^(log₂ 7)` bounds. Master case 3 uses forcing regularity, and
  the Akra–Bazzi interface states its restricted monomial/floor-recurrence scope.
- **Chapter 5:** the existing longest-streak upper and lower bounds are visible in
  the fourth-edition guide and public checks, including the `n ≥ 16` premise.
- **Chapter 6:** documentation now states that `ArrayMaxHeapFrom` constrains every
  parent at or after `start`, rather than only descendants of one node.

The cost model excludes indexing, allocation, scalar bit complexity, and internal
copying unless a theorem says otherwise. Focused regressions, chapter interfaces,
trust checks, repository checks, and the full build passed.
