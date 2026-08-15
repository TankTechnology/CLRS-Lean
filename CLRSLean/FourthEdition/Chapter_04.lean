import CLRSLean.FourthEdition.Chapter_04.Section_04_1_Multiplying_Square_Matrices
import CLRSLean.FourthEdition.Chapter_04.Section_04_2_Strassen_Algorithm
import CLRSLean.FourthEdition.Chapter_04.Section_04_3_Substitution_Method
import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method
import CLRSLean.FourthEdition.Chapter_04.Section_04_5_Master_Theorem
import CLRSLean.FourthEdition.Chapter_04.Section_04_6_Continuous_Master_Theorem
import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi

/-!
# Chapter 4 — Divide-and-Conquer

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 4.1--4.7 are native fourth-edition sections:

* [Section 4.1 — Multiplying square matrices](CLRSLean/FourthEdition/Chapter_04/Section_04_1_Multiplying_Square_Matrices/):
  the recursive eight-product `SQUARE-MATRIX-MULTIPLY-RECURSIVE` and its
  {lit}`Θ(n³)` runtime.
* [Section 4.2 — Strassen's algorithm for matrix multiplication](CLRSLean/FourthEdition/Chapter_04/Section_04_2_Strassen_Algorithm/):
  the seven-product block algebra, the recursive power-of-two algorithm, and
  its {lit}`Θ(n^(log₂ 7))` runtime.
* [Section 4.3 — The substitution method](CLRSLean/FourthEdition/Chapter_04/Section_04_3_Substitution_Method/):
  one-step upper-bound, lower-bound, and sandwich substitution templates.
* [Section 4.4 — The recursion-tree method](CLRSLean/FourthEdition/Chapter_04/Section_04_4_Recursion_Tree_Method/):
  exact additive level unrolling and envelope bounds.
* [Section 4.5 — The master method](CLRSLean/FourthEdition/Chapter_04/Section_04_5_Master_Theorem/):
  normalized recurrence expansion and the three Master-style exact-power
  criteria (including the polylog case-2 extension).
* [Section 4.6 — Proof of the continuous master theorem](CLRSLean/FourthEdition/Chapter_04/Section_04_6_Continuous_Master_Theorem/):
  the real geometric-series core and the three continuous cases, bridged to the
  discrete comparison scales.
* [Section 4.7 — Akra–Bazzi recurrences](CLRSLean/FourthEdition/Chapter_04/Section_04_7_Akra_Bazzi/):
  the recurrence hypotheses, the root equation, the multi-branch root
  uniqueness and nonnegativity, the scale-invariance bridge, and the integral
  asymptotic form with its explicit polynomial-smoothness predicate.

Declarations retain the `CLRS.Chapter04` namespace during the compatibility
period; the third-edition-numbered imports {lit}`CLRSLean.Chapter_04` and
{lit}`CLRSLean.Chapter_04.Section_04_*` forward to these sources.

## Coverage boundary

The native sections close the §4.1--§4.7 boundary.  Maximum subarray moves to
Online Material; the third-edition-only all-input Master-theorem detail remains
in the legacy tree as its own source.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
