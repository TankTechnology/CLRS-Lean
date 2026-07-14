import CLRSLean.Chapter_28.Section_28_1_LUP_Decomposition
import CLRSLean.Chapter_28.Section_28_2_3_Matrix_Inversion_LS

/-!
# Chapter 28. Matrix Operations

Chapter 28 covers algorithms for solving systems of linear equations,
inverting matrices, symmetric positive-definite matrices, and least-squares
approximation.

* Section 28.1 - Solving systems of linear equations with LUP decomposition:
  {lit}`partial`.  The file defines `LUDecomp`, `forwardSubst`, `backSubst`,
  `lupDecomp`, and `lupSolve` with full theorem interfaces and deferred proof
  obligations (`sorry`).  The definitions are noncomputable (`Classical.choice`);
  a constructive, algorithmic realization remains future work.

* Section 28.2–28.3 - Matrix inversion, SPD matrices, and least-squares
  approximation: {lit}`partial`.  The file defines `matrixInverse` (column-by-column
  via LUP-SOLVE), the `SPDMatrix` predicate, `LDLTDecomp`, `ldltDecomp`,
  `leastSquares` (via normal equations), and `CholeskyDecomp`.  Key theorems
  (`A * A⁻¹ = I`, `leastSquares_residual_orthogonal`, `leastSquares_optimal`)
  have interfaces; complex proofs and the `A⁻¹ * A = I` direction are deferred
  (`sorry`).  The definitions inherit noncomputability from §28.1.

The remaining section (28.4) is not yet represented:

* Section 28.4 - The symmetric indefinite decomposition
-/

namespace CLRS
namespace Chapter28
end Chapter28
end CLRS
