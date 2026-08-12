import CLRSLean.Chapter_28

namespace CLRS
namespace Chapter28

open Matrix

-- Section 28.1: LUP decomposition (Theorem 28.1), substitution (Lemmas 28.1-28.2), LUP-SOLVE
#check IsUpperTriangular
#check IsLowerTriangular
#check IsUnitLowerTriangular
#check exists_lup_decomposition
#check forwardSubst
#check forwardSubst_spec
#check backSubst
#check backSubst_spec
#check lupSolve
#check lupSolve_correct
#check lup_solve_correct
#check exists_solution_of_nonsingular
#check unique_solution_of_nonsingular
#check unique_solution_unitLowerTriangular
#check unique_solution_upperTriangular
#check det_eq_sign_mul_det_of_lup
#check det_ne_zero_of_lup
#check substitutionCost_isBigO
#check lupDecompositionCost_isBigO
#check matrixInversionCost_isBigO
#check choleskyCost_isBigO

-- Section 28.2: inversion from LUP (Theorem 28.2)
#check permMatrix_inv
#check permMatrix_mul_inv
#check inv_eq_lup

-- Section 28.3: SPD matrices, Cholesky (Theorem 28.3), least squares (28.4)
#check IsSymPosDef
#check isSymPosDef_iff_posDef
#check IsSymPosDef.det_pos
#check IsSymPosDef.diag_pos
#check IsSymPosDef.mulVec_injective
#check posDef_mul_transpose
#check residualSq
#check normal_equations_minimizes
#check normal_equations_unique
#check least_squares_closed_form
#check least_squares_closed_form_minimizes
#check choleskySchur
#check schur_quadratic_form
#check cholesky_schur_complement
#check IsLowerTriangularPosDiag
#check choleskyFactor
#check cholesky_decomposition
#check cholesky_unique

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSymPosDef A) : 0 < A.det :=
  hA.det_pos

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSymPosDef A) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ, IsLowerTriangularPosDiag L ∧ A = L * Lᵀ :=
  cholesky_decomposition A hA

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : Function.Injective A.mulVec)
    (b : Fin m → ℝ) :
    residualSq A b ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ≤ residualSq A b 0 :=
  least_squares_closed_form_minimizes A b hA 0

end Chapter28
end CLRS
