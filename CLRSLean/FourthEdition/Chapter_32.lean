import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher

/-!
# Chapter 32 — String Matching

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Section 32.1 is a native fourth-edition section (the string model with the
naive matcher), imported directly from
[Section 32.1](CLRSLean/FourthEdition/Chapter_32/Section_32_1_String_Model/).
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_32` and
{lit}`CLRSLean.Chapter_32.Section_32_*` forward to these sources.

## Coverage boundary

The naive matcher development is reused.  Section 32.2 (the Rabin–Karp
algorithm) is proved: the base-`d` modular hash, the O(1) incremental update,
and the soundness, completeness, and agreement-with-`naiveMatcher` theorems.
Finite automata, KMP, and suffix arrays remain named gaps.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
