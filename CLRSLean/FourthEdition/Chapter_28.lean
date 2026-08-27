import CLRSLean.Chapter_28
import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations
import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP
import CLRSLean.FourthEdition.Chapter_28.Section_28_2_Inverting_Matrices
import CLRSLean.FourthEdition.Chapter_28.Section_28_3_Symmetric_Positive_Definite

/-!
# Chapter 28 — Matrix Operations

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 28.1--28.3 are native fourth-edition sections (solving systems of
linear equations via LUP decomposition, inverting matrices, and symmetric
positive-definite matrices with least-squares approximation), imported
directly from
[Section 28.1](CLRSLean/FourthEdition/Chapter_28/Section_28_1_Linear_Equations/),
[Section 28.2](CLRSLean/FourthEdition/Chapter_28/Section_28_2_Inverting_Matrices/),
and
[Section 28.3](CLRSLean/FourthEdition/Chapter_28/Section_28_3_Symmetric_Positive_Definite/).
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_28` and
{lit}`CLRSLean.Chapter_28.Section_28_*` forward to these sources.

## Coverage boundary

The native sections supply the represented fourth-edition matrix-operations
sections (CLRS Theorem 28.1 and Lemmas 28.1--28.2).  The constructive
Theorem 28.1 layer is exposed by {lit}`lupDecomposeWithCost`: it explicitly
scans for a nonzero pivot, swaps rows, performs pointwise Gaussian elimination,
recurses on the Schur block, and returns either factors or failure.
{lit}`lupDecomposeWithCost_correct` proves that every nonsingular input returns
a unit-lower-triangular factor, an upper-triangular factor with nonzero
diagonal, and the exact equation {lit}`P·A=L·U`, while the same execution's
counter is at most {lit}`4n³`.  Failure is equivalent to a zero determinant.

The costed solver {lit}`lupSolveWithCost` erases to the existing
{lit}`lupSolve`, inherits its solution theorem, and records at most
{lit}`2n²` field operations.  These are exact-field unit-cost results with
decidable zero testing; floating-point stability, mutable storage, allocation,
and bit/RAM costs remain outside this boundary.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
