# Chapters 10–12 Repair Record

Issues [#352](https://github.com/TankTechnology/CLRS-Lean/issues/352) through
[#354](https://github.com/TankTechnology/CLRS-Lean/issues/354) were resolved.

- **Chapter 10:** legal capacity and pointer predicates, empty constructors, and
  update preservation now define the array-state contract. Circular queues reject
  invalid states. Linked-list search exposes `none` completeness, first-match
  prefixes, and minimum indices; deletion remains an all-equal-keys operation.
- **Chapter 11:** perfect-hash injectivity is limited to stored keys, so legal
  nonmember collisions are allowed. Query regressions and construction-cost
  bridges use the corrected domain.
- **Chapter 12:** the guide states strict-order set semantics and duplicate
  suppression. `RepresentsW` constrains child structure and footprint without
  claiming stored-parent consistency. Expected height is marked as supplementary
  material rather than fourth-edition Section 12.4.

Chapter builds, old and new interfaces, semantic regressions, trust checks, and
the full library regression passed.
