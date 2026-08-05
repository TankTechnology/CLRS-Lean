import CLRSLean.Chapter_28

<<<<<<< HEAD
/-!
# Chapter 28 Interface Test

Verifies that the public Section 28.1 LUP-decomposition declarations are
available through the chapter guide and that the main theorem has the
advertised downstream interface.
-/

namespace CLRS
namespace Chapter28

#check IsUpperTriangular
#check IsLowerTriangular
#check IsUnitLowerTriangular
#check elimination
#check elimination_unitLowerTriangular
#check elimination_mul_col_zero
#check det_unitLowerTriangular
#check det_block_schur
#check exists_lup_decomposition
#check permMatrix_inv
#check permMatrix_mul_inv
#check inv_eq_lup

example {F : Type} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) F),
      IsUnitLowerTriangular L ∧ IsUpperTriangular U ∧
        σ.permMatrix F * A = L * U :=
  exists_lup_decomposition A hA

example {F : Type} [Field F] {n : ℕ}
    {A L U : Matrix (Fin n) (Fin n) F} {σ : Equiv.Perm (Fin n)}
    (hLUP : σ.permMatrix F * A = L * U) :
    A⁻¹ = U⁻¹ * L⁻¹ * σ.permMatrix F :=
  inv_eq_lup hLUP

#print axioms exists_lup_decomposition
#print axioms inv_eq_lup
||||||| parent of d4fbcbf (chore(ch28): polish docs, status board, and add interface test)
=======
namespace CLRS
namespace Chapter28

open Matrix

-- Section 28.1: LUP decomposition (Theorem 28.1) and LUP-SOLVE
#check IsUpperTriangular
#check IsLowerTriangular
#check IsUnitLowerTriangular
#check exists_lup_decomposition
#check lup_solve_correct
#check exists_solution_of_nonsingular

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

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSymPosDef A) : 0 < A.det :=
  hA.det_pos

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSymPosDef A) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ, IsLowerTriangularPosDiag L ∧ A = L * Lᵀ :=
  cholesky_decomposition A hA

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hA : Function.Injective A.mulVec)
    (b : Fin m → ℝ) :
    residualSq A b ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ≤ residualSq A b 0 :=
  least_squares_closed_form_minimizes A b hA 0
>>>>>>> d4fbcbf (chore(ch28): polish docs, status board, and add interface test)

end Chapter28
end CLRS
