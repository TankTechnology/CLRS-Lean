import CLRSLean.Chapter_32

/-!
# Chapter 32 — String Matching

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_32`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The naive matcher development is reused.  Section 32.2 (the Rabin–Karp
algorithm) is proved: the base-`d` modular hash, the O(1) incremental update,
and the soundness, completeness, and agreement-with-`naiveMatcher` theorems.
Finite automata, KMP, and suffix arrays remain named gaps.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
