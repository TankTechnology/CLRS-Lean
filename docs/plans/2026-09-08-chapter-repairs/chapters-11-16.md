# Chapters 11 and 13–16 Repair Record

Issues [#353](https://github.com/TankTechnology/CLRS-Lean/issues/353) and
[#355](https://github.com/TankTechnology/CLRS-Lean/issues/355) through
[#358](https://github.com/TankTechnology/CLRS-Lean/issues/358) were resolved.

- **Chapter 11:** randomized perfect-hash construction now returns a concrete
  table and an attached cost, with injectivity scoped to stored keys.
- **Chapter 13:** pointer rotations reconnect roots and parent links. Strengthened
  representation invariants cover sentinels, ownership, and parent-child
  consistency. Counted updates refine the functional operations.
- **Chapter 14:** rod cutting, matrix chain, LCS, and optimal BST now expose actual
  dynamic-programming executions with table or cache invariants, reconstruction,
  erasure, and attached work bounds.
- **Chapter 15:** offline caching states the empty-cache boundary for arbitrary
  capacity without overstating the existing nonempty-cache theorem.
- **Chapter 16:** mixed stack traces now have an amortized bound rather than only a
  single-MULTIPOP estimate.

Targeted behavior tests cover invalid perfect-hash candidates, root and internal
rotations, sentinel edge cases, dynamic-programming tables and reconstructions,
empty caches, and mixed stack traces. Interface and axiom checks passed for every
new public theorem.
