# Chapters 1–3 Repair Record

Issues [#345](https://github.com/TankTechnology/CLRS-Lean/issues/345) through
[#347](https://github.com/TankTechnology/CLRS-Lean/issues/347) were resolved.

- **Chapter 1:** fourth-edition navigation now points to Chapters 15 and 21 for
  greedy algorithms and MSTs. The guide describes both `Option`-returning APIs
  and total functions whose meaningful behavior is guarded by premises.
- **Chapter 2:** the counted insertion-sort execution now connects actual
  comparison counts to the worst-case quadratic bound. The public guide and
  interface tests expose the bridge.
- **Chapter 3:** helper-module section references now use fourth-edition numbering
  consistently.

Focused interface tests, trust checks, repository checks, and the full Lean build
passed. See the [unified verification record](verification.md).
