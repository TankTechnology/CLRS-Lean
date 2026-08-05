import CLRSLean.Chapter_28

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

example {F : Type} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) F),
      IsUnitLowerTriangular L ∧ IsUpperTriangular U ∧
        σ.permMatrix F * A = L * U :=
  exists_lup_decomposition A hA

#print axioms exists_lup_decomposition

end Chapter28
end CLRS
