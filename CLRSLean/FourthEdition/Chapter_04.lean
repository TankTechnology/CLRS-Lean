import CLRSLean.Chapter_04
import CLRSLean.FourthEdition.Chapter_04.Section_04_1_Multiplying_Square_Matrices
import CLRSLean.FourthEdition.Chapter_04.Section_04_6_Continuous_Master_Theorem
import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi

/-!
# Chapter 4 — Divide-and-Conquer

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 4.1, 4.6, and 4.7 are native fourth-edition sections:

* [Section 4.1 — Multiplying square matrices](CLRSLean/FourthEdition/Chapter_04/Section_04_1_Multiplying_Square_Matrices/):
  the recursive eight-product `SQUARE-MATRIX-MULTIPLY-RECURSIVE` and its
  {lit}`Θ(n³)` runtime.
* [Section 4.6 — Proof of the continuous master theorem](CLRSLean/FourthEdition/Chapter_04/Section_04_6_Continuous_Master_Theorem/):
  the real geometric-series core and the three continuous cases, bridged to the
  discrete comparison scales.
* [Section 4.7 — Akra–Bazzi recurrences](CLRSLean/FourthEdition/Chapter_04/Section_04_7_Akra_Bazzi/):
  the recurrence hypotheses, the root equation, the multi-branch root
  uniqueness and nonnegativity, the scale-invariance bridge, and the integral
  asymptotic form with its explicit polynomial-smoothness predicate.

Sections 4.2–4.5 remain sourced from the legacy
{lit}`CLRSLean.Chapter_04` guide (Strassen's algorithm, the substitution method,
the recursion-tree method, and the master method); their declarations keep their
current namespaces during the compatibility period.

## Coverage boundary

The native sections close the §4.1, §4.6, and §4.7 boundary.  Maximum subarray
moves to Online Material.  The full multi-branch Akra–Bazzi integral bound and
the recurrence-to-integral substitution comparison remain recorded gaps (see
§4.7).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
