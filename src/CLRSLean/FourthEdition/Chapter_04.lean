import CLRSLean.FourthEdition.Chapter_04.Section_04_1_Multiplying_Square_Matrices
import CLRSLean.FourthEdition.Chapter_04.Section_04_2_Strassen_Algorithm
import CLRSLean.FourthEdition.Chapter_04.Section_04_3_Substitution_Method
import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method
import CLRSLean.FourthEdition.Chapter_04.Section_04_5_Master_Theorem
import CLRSLean.FourthEdition.Chapter_04.Section_04_6_Continuous_Master_Theorem
import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi
import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi.Generalized
import CLRSLean.FourthEdition.Chapter_04.MatrixExecution

/-!
# Chapter 4 — Divide-and-Conquer

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 4.1--4.7 are native fourth-edition sections:

* [Section 4.1 — Multiplying square matrices](CLRSLean/FourthEdition/Chapter_04/Section_04_1_Multiplying_Square_Matrices/):
  the recursive eight-product `SQUARE-MATRIX-MULTIPLY-RECURSIVE` and its
  {lit}`Θ(n³)` scalar work, proved from the counted execution on side lengths
  {lit}`2^k`.
* [Section 4.2 — Strassen's algorithm for matrix multiplication](CLRSLean/FourthEdition/Chapter_04/Section_04_2_Strassen_Algorithm/):
  the seven-product block algebra, the recursive power-of-two algorithm, and
  its {lit}`Θ(n^(log₂ 7))` scalar work from the same counted execution.
* [Section 4.3 — The substitution method](CLRSLean/FourthEdition/Chapter_04/Section_04_3_Substitution_Method/):
  one-step upper-bound, lower-bound, and sandwich substitution templates.
* [Section 4.4 — The recursion-tree method](CLRSLean/FourthEdition/Chapter_04/Section_04_4_Recursion_Tree_Method/):
  exact additive level unrolling, explicit finite branching trees, internal
  level-plus-leaf decomposition, reusable geometric bounds, and the textbook
  {lit}`3T(n/4)+cn²` and {lit}`T(n/3)+T(2n/3)+cn` calculations.  Alongside the
  exact-real common-depth model, natural-size floor/ceiling trees now execute
  to their base cases, permit unequal child depths, and agree exactly with
  independently stated recurrence equations. Their actual total costs now have
  proved {lit}`Θ(n²)` and {lit}`Θ(n log n)` bounds for positive local-cost
  coefficients and nonnegative base costs.
* [Section 4.5 — The master method](CLRSLean/FourthEdition/Chapter_04/Section_04_5_Master_Theorem/):
  normalized recurrence expansion and the three Master-style exact-power
  criteria (including the polylog case-2 extension), with case 3 derived from
  eventual forcing regularity rather than an assumed solution bound.
* [Section 4.6 — Proof of the continuous master theorem](CLRSLean/FourthEdition/Chapter_04/Section_04_6_Continuous_Master_Theorem/):
  the real geometric-series core and the three continuous cases, bridged to the
  discrete comparison scales.
* [Section 4.7 — Akra–Bazzi recurrences](CLRSLean/FourthEdition/Chapter_04/Section_04_7_Akra_Bazzi/):
  the recurrence hypotheses, the root equation, the multi-branch root
  uniqueness and nonnegativity, the scale-invariance bridge, and the integral
  asymptotic form for every nonnegative root and forcing exponent under the
  explicit {lit}`PolynomialGrowth` monomial sandwich and floor recurrence.

Declarations retain the `CLRS.Chapter04` namespace during the compatibility
period; the third-edition-numbered imports {lit}`CLRSLean.Chapter_04` and
{lit}`CLRSLean.Chapter_04.Section_04_*` forward to these sources.

## Coverage boundary

The proved boundary consists of the models and hypotheses stated above. Matrix
execution uses depth-indexed power-of-two squares; {lit}`padOne` embeds one such
square into the next depth and is not an arbitrary-dimension padding interface.
Its counter charges scalar ring operations, excluding indexing, allocation, and
the internal cost of each scalar operation. The continuous layer is a real-valued
geometric calculation at natural depth. Akra–Bazzi retains monotone forcing
between positive multiples of one monomial and explicit floor children; it does
not assert unrestricted forcing or perturbations. Maximum subarray belongs to
Online Material; the third-edition all-input Master detail remains in the legacy
tree as its own source.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
