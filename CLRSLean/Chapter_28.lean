import CLRSLean.Chapter_28.Section_28_1_Linear_Equations
import CLRSLean.Chapter_28.Section_28_2_Inverting_Matrices
import CLRSLean.Chapter_28.Section_28_3_Symmetric_Positive_Definite

/-! # Chapter 28 - Matrix Operations

Chapter 28 studies algorithms for matrices over the reals: solving systems of
linear equations, inverting matrices, and least-squares approximation.  It opens
with the LUP decomposition (Theorem 28.1), which underlies Gaussian elimination,
determinants, and matrix inversion.

## Sections

* 28.1 Solving systems of linear equations.
  Main declarations:
  {lit}`CLRS.Chapter28.IsUpperTriangular`,
  {lit}`CLRS.Chapter28.IsLowerTriangular`,
  {lit}`CLRS.Chapter28.IsUnitLowerTriangular`,
  and {lit}`CLRS.Chapter28.exists_lup_decomposition`.
* 28.2 Inverting matrices.
  Main declaration: {lit}`CLRS.Chapter28.inv_eq_lup`.
* 28.3 Symmetric positive-definite matrices and least-squares approximation.
  Main declarations:
  {lit}`CLRS.Chapter28.IsSymPosDef`,
  {lit}`CLRS.Chapter28.cholesky_decomposition`,
  {lit}`CLRS.Chapter28.normal_equations_minimizes`,
  and {lit}`CLRS.Chapter28.cholesky_schur_complement`.
-/
