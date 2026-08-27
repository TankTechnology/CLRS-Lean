import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP.Execution

/-!
# CLRS Section 28.1 - Executable LUP correctness

Successful recursive results satisfy the exact triangular and factorization
contract.  Nonsingular inputs succeed, so failure characterizes singularity.
-/

namespace CLRS
namespace Chapter28

open Matrix

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
private theorem assembleLUPFactors_correct {n : Nat}
    (A B D : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (p : Fin (n + 1))
    (hB0 : B 0 0 ≠ 0)
    (hB : B = (Equiv.swap 0 p).permMatrix F * A)
    (hD : D = elimination B hB0 * B)
    (child : LUPFactors n F)
    (hchildL : IsUnitLowerTriangular child.lower)
    (hchildU : IsUpperTriangular child.upper)
    (hchildFac :
      let M : Matrix (Fin n) (Fin n) F := fun i j => D (Fin.succ i) (Fin.succ j)
      child.perm.permMatrix F * M = child.lower * child.upper) :
    let factors := assembleLUPFactors B D (Equiv.swap 0 p) child
    IsUnitLowerTriangular factors.lower ∧
      IsUpperTriangular factors.upper ∧
      factors.perm.permMatrix F * A = factors.lower * factors.upper := by
  let re : Fin (n + 1) ≃ Fin 1 ⊕ Fin n := execFinOneSumFin n
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) F := elimination B hB0
  let M : Matrix (Fin n) (Fin n) F := fun i j => D (Fin.succ i) (Fin.succ j)
  let α : Matrix (Fin 1) (Fin 1) F := fun _ _ => D 0 0
  let v : Matrix (Fin 1) (Fin n) F := fun _ j => D 0 (Fin.succ j)
  let mult : Matrix (Fin n) (Fin 1) F := fun i _ => B (Fin.succ i) 0 / B 0 0
  let P₁ : Matrix (Fin n) (Fin n) F := child.perm.permMatrix F
  have hMfac : P₁ * M = child.lower * child.upper := by
    simpa [P₁, M] using hchildFac
  let diagP : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0 P₁).reindex re.symm re.symm
  let E' : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 mult
      (1 : Matrix (Fin n) (Fin n) F)).reindex re.symm re.symm
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 (P₁ * mult) child.lower).reindex
      re.symm re.symm
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    (Matrix.fromBlocks α v (0 : Matrix (Fin n) (Fin 1) F) child.upper).reindex
      re.symm re.symm
  let σP : Equiv.Perm (Fin (n + 1)) := liftTrailingPerm child.perm
  let σ₀ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p * σP
  have hDcol : ∀ i : Fin n, D (Fin.succ i) 0 = 0 := by
    intro i
    rw [hD]
    exact elimination_mul_col_zero B hB0 i
  have hDblocks : D.reindex re re =
      Matrix.fromBlocks α v (0 : Matrix (Fin n) (Fin 1) F) M := by
    rw [Matrix.ext_iff_blocks]
    constructor
    · ext i j
      simp [re, α, Matrix.reindex_apply, Matrix.toBlocks₁₁]
    · constructor
      · ext i j
        simp [re, v, Matrix.reindex_apply, Matrix.toBlocks₁₂]
      · constructor
        · ext i j
          simp [re, Matrix.reindex_apply, Matrix.toBlocks₂₁]
          exact hDcol i
        · ext i j
          simp [re, M, Matrix.reindex_apply, Matrix.toBlocks₂₂]
  have hEblocks : E.reindex re re =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F)
        (0 : Matrix (Fin 1) (Fin n) F) (-mult) (1 : Matrix (Fin n) (Fin n) F) := by
    rw [Matrix.ext_iff_blocks]
    constructor
    · ext i j
      simp [re, E, elimination, Matrix.reindex_apply, Matrix.toBlocks₁₁, Matrix.one_apply]
      exact Subsingleton.elim i j
    · constructor
      · ext i j
        simp [re, E, elimination, Matrix.reindex_apply, Matrix.toBlocks₁₂, eq_comm]
      · constructor
        · ext i j
          simp [re, E, elimination, mult, Matrix.reindex_apply, Matrix.toBlocks₂₁]
          ring
        · ext i j
          simp [re, E, elimination, Matrix.reindex_apply, Matrix.toBlocks₂₂, Matrix.one_apply]
  have hEinv : E' * E = 1 := by
    apply (reindexRingEquiv F re).injective
    rw [map_mul, map_one]
    rw [show (reindexRingEquiv F re) E' = Matrix.fromBlocks 1 0 mult
        (1 : Matrix (Fin n) (Fin n) F) by
      simp [E', Matrix.reindex_apply, Matrix.submatrix_submatrix]]
    rw [show (reindexRingEquiv F re) E = Matrix.fromBlocks 1 0 (-mult)
        (1 : Matrix (Fin n) (Fin n) F) by
      simpa using hEblocks]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hσP : Equiv.Perm.permMatrix F σP = diagP := by
    dsimp [σP, liftTrailingPerm, diagP]
    rw [conjPermMatrix re (Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) child.perm)]
    rw [← fromBlocks_one_zero_zero_permMatrix child.perm]
    rfl
  have hDiagE'D : diagP * E' * D = L * U := by
    apply (reindexRingEquiv F re).injective
    rw [map_mul, map_mul]
    rw [show (reindexRingEquiv F re) D = Matrix.fromBlocks α v
        (0 : Matrix (Fin n) (Fin 1) F) M by simpa using hDblocks]
    rw [map_mul]
    rw [show (reindexRingEquiv F re) diagP = Matrix.fromBlocks 1 0 0 P₁ by
      simp [diagP, Matrix.reindex_apply, Matrix.submatrix_submatrix]]
    rw [show (reindexRingEquiv F re) E' = Matrix.fromBlocks 1 0 mult
        (1 : Matrix (Fin n) (Fin n) F) by
      simp [E', Matrix.reindex_apply, Matrix.submatrix_submatrix]]
    rw [show (reindexRingEquiv F re) L = Matrix.fromBlocks 1 0 (P₁ * mult) child.lower by
      simp [L, Matrix.reindex_apply, Matrix.submatrix_submatrix]]
    rw [show (reindexRingEquiv F re) U = Matrix.fromBlocks α v
        (0 : Matrix (Fin n) (Fin 1) F) child.upper by
      simp [U, Matrix.reindex_apply, Matrix.submatrix_submatrix]]
    simp [Matrix.fromBlocks_multiply, hMfac]
  have hBD : B = E' * D := by
    calc
      B = 1 * B := by rw [one_mul]
      _ = (E' * E) * B := by rw [hEinv]
      _ = E' * (E * B) := by rw [Matrix.mul_assoc]
      _ = E' * D := by rw [hD]
  have hDiagB : diagP * B = L * U := by
    calc
      diagP * B = diagP * (E' * D) := by rw [hBD]
      _ = (diagP * E') * D := by rw [Matrix.mul_assoc]
      _ = L * U := hDiagE'D
  have hEq : σ₀.permMatrix F * A = L * U := by
    calc
      σ₀.permMatrix F * A = ((Equiv.swap 0 p) * σP).permMatrix F * A := by rfl
      _ = (σP.permMatrix F * (Equiv.swap 0 p).permMatrix F) * A := by
        rw [Matrix.permMatrix_mul]
      _ = σP.permMatrix F * ((Equiv.swap 0 p).permMatrix F * A) := by
        rw [Matrix.mul_assoc]
      _ = σP.permMatrix F * B := by rw [hB]
      _ = diagP * B := by rw [hσP]
      _ = L * U := hDiagB
  have hL : IsUnitLowerTriangular L := by
    constructor
    · intro i j hij
      by_cases hi : i = 0
      · have hj : j ≠ 0 := ne_zero_of_lt_succ hij
        dsimp only [L]
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        have hri : re i = Sum.inl (⟨0, by omega⟩ : Fin 1) := by
          dsimp [re, execFinOneSumFin]
          simp [hi]
        have hrj : re j = Sum.inr (j.pred hj) := by
          dsimp [re, execFinOneSumFin]
          simp [hj]
        rw [hri, hrj]
        simp
      · have hj : j ≠ 0 := ne_zero_of_lt_succ hij
        dsimp only [L]
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        have hri : re i = Sum.inr (i.pred hi) := by
          dsimp [re, execFinOneSumFin]
          simp [hi]
        have hrj : re j = Sum.inr (j.pred hj) := by
          dsimp [re, execFinOneSumFin]
          simp [hj]
        rw [hri, hrj]
        simp
        apply hchildL.1
        have hsi : i = Fin.succ (i.pred hi) := (Fin.succ_pred i hi).symm
        have hsj : j = Fin.succ (j.pred hj) := (Fin.succ_pred j hj).symm
        rw [hsi, hsj] at hij
        exact Fin.succ_lt_succ_iff.mp hij
    · intro i
      by_cases hi : i = 0
      · dsimp only [L]
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        have hri : re i = Sum.inl (⟨0, by omega⟩ : Fin 1) := by
          dsimp [re, execFinOneSumFin]
          simp [hi]
        rw [hri]
        simp
      · dsimp only [L]
        rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
        have hri : re i = Sum.inr (i.pred hi) := by
          dsimp [re, execFinOneSumFin]
          simp [hi]
        rw [hri]
        simp
        exact hchildL.2 (i.pred hi)
  have hU : IsUpperTriangular U := by
    intro i j hji
    by_cases hj : j = 0
    · have hi : i ≠ 0 := ne_zero_of_lt hji
      dsimp only [U]
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      have hrj : re j = Sum.inl (⟨0, by omega⟩ : Fin 1) := by
        dsimp [re, execFinOneSumFin]
        simp [hj]
      have hri : re i = Sum.inr (i.pred hi) := by
        dsimp [re, execFinOneSumFin]
        simp [hi]
      rw [hrj, hri]
      simp
    · have hi : i ≠ 0 := ne_zero_of_lt hji
      dsimp only [U]
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      have hrj : re j = Sum.inr (j.pred hj) := by
        dsimp [re, execFinOneSumFin]
        simp [hj]
      have hri : re i = Sum.inr (i.pred hi) := by
        dsimp [re, execFinOneSumFin]
        simp [hi]
      rw [hrj, hri]
      simp
      apply hchildU
      have hsj : j = Fin.succ (j.pred hj) := (Fin.succ_pred j hj).symm
      have hsi : i = Fin.succ (i.pred hi) := (Fin.succ_pred i hi).symm
      rw [hsj, hsi] at hji
      exact Fin.succ_lt_succ_iff.mp hji
  change IsUnitLowerTriangular
      (assembleLUPFactors B D (Equiv.swap 0 p) child).lower ∧
    IsUpperTriangular (assembleLUPFactors B D (Equiv.swap 0 p) child).upper ∧
    (assembleLUPFactors B D (Equiv.swap 0 p) child).perm.permMatrix F * A =
      (assembleLUPFactors B D (Equiv.swap 0 p) child).lower *
        (assembleLUPFactors B D (Equiv.swap 0 p) child).upper
  simpa [assembleLUPFactors, re, α, v, mult, P₁, L, U, σP, σ₀,
    liftTrailingPerm] using And.intro hL (And.intro hU hEq)

omit [DecidableEq F] in
/-- Direct row lookup agrees with multiplying by the selected swap matrix. -/
theorem pivotedMatrix_eq_permMatrix_mul {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (p : Fin (n + 1)) :
    pivotedMatrix A p = (Equiv.swap 0 p).permMatrix F * A := by
  ext i j
  rw [permMatrix_mul_apply]
  rfl

/-- Every factor triple returned by the recursive execution is a valid LUP
decomposition. -/
theorem lupDecomposeWithCost_sound : ∀ {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) (factors : LUPFactors n F),
    (lupDecomposeWithCost n A).result = some factors →
      IsUnitLowerTriangular factors.lower ∧
        IsUpperTriangular factors.upper ∧
        factors.perm.permMatrix F * A = factors.lower * factors.upper
  | 0, A, factors, hresult => by
      have hf : (⟨1, 1, 1⟩ : LUPFactors 0 F) = factors := by
        exact Option.some.inj (by simpa [lupDecomposeWithCost] using hresult)
      subst factors
      constructor
      · simp [IsUnitLowerTriangular, IsLowerTriangular]
      · constructor
        · simp [IsUpperTriangular]
        · ext i j
          exact Fin.elim0 i
  | n + 1, A, factors, hresult => by
      cases hpivot : (findPivotWithCost A).pivot with
      | none =>
          simp [lupDecomposeWithCost, hpivot] at hresult
      | some p =>
          let pivotPerm : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p.1
          let B := pivotedMatrix A p.1
          have hp0 : A p.1 0 ≠ 0 := p.2
          have hB0 : B 0 0 ≠ 0 := by
            simpa [B, pivotedMatrix] using hp0
          let eliminated := eliminateWithCost B hB0
          let M : Matrix (Fin n) (Fin n) F :=
            fun i j => eliminated.value (Fin.succ i) (Fin.succ j)
          let child := lupDecomposeWithCost n M
          cases hchild : child.result with
          | none =>
              have hchild' :
                  (lupDecomposeWithCost n M).result = none := by
                simpa [child] using hchild
              simp [lupDecomposeWithCost, hpivot, B, eliminated, M, hchild'] at hresult
          | some childFactors =>
              have hchild' :
                  (lupDecomposeWithCost n M).result = some childFactors := by
                simpa [child] using hchild
              have hfactor :
                  assembleLUPFactors B eliminated.value pivotPerm childFactors = factors := by
                apply Option.some.inj
                simpa [lupDecomposeWithCost, hpivot, pivotPerm, B, hp0, hB0,
                  eliminated, M, child, hchild'] using hresult
              have hchildResult :
                  (lupDecomposeWithCost n M).result = some childFactors := by
                exact hchild'
              have hchildCorrect := lupDecomposeWithCost_sound M childFactors hchildResult
              subst factors
              apply assembleLUPFactors_correct A B eliminated.value p.1 hB0
              · exact pivotedMatrix_eq_permMatrix_mul A p.1
              · exact eliminateWithCost_value B hB0
              · exact hchildCorrect.1
              · exact hchildCorrect.2.1
              · simpa [M] using hchildCorrect.2.2

/-- Every nonsingular matrix makes the explicit pivot/elimination recursion
return a factor triple. -/
theorem lupDecomposeWithCost_nonsingular : ∀ {n : Nat}
    (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
      ∃ factors, (lupDecomposeWithCost n A).result = some factors
  | 0, _A, _hA => by
      exact ⟨⟨1, 1, 1⟩, rfl⟩
  | n + 1, A, hA => by
      cases hpivot : (findPivotWithCost A).pivot with
      | none =>
          have hcol : ∀ p : Fin (n + 1), A p 0 = 0 :=
            (findPivotWithCost_eq_none A).1 hpivot
          exact False.elim (hA (det_eq_zero_of_col_zero hcol))
      | some p =>
          let B := pivotedMatrix A p.1
          have hB0 : B 0 0 ≠ 0 := by
            simpa [B, pivotedMatrix] using p.2
          let eliminated := eliminateWithCost B hB0
          let M : Matrix (Fin n) (Fin n) F :=
            fun i j => eliminated.value (Fin.succ i) (Fin.succ j)
          have hBdet : B.det ≠ 0 := by
            dsimp [B]
            rw [pivotedMatrix_eq_permMatrix_mul, Matrix.det_mul]
            have hrinv :
                (Equiv.swap 0 p.1)⁻¹.permMatrix F * (Equiv.swap 0 p.1).permMatrix F = 1 := by
              rw [← Matrix.permMatrix_mul]
              simp
            have hdetPerm : ((Equiv.swap 0 p.1).permMatrix F).det ≠ 0 :=
              Matrix.det_ne_zero_of_left_inverse hrinv
            exact mul_ne_zero hdetPerm hA
          have hDdet : eliminated.value.det ≠ 0 := by
            rw [eliminateWithCost_value, Matrix.det_mul]
            rw [det_unitLowerTriangular (elimination_unitLowerTriangular B hB0)]
            simpa using hBdet
          have hDcol : ∀ i : Fin n, eliminated.value (Fin.succ i) 0 = 0 := by
            exact eliminateWithCost_col_zero B hB0
          have hblock : eliminated.value.det = B 0 0 * M.det := by
            rw [det_block_schur eliminated.value hDcol]
            have h00 : eliminated.value 0 0 = B 0 0 := by
              rw [eliminateWithCost_value]
              exact elimination_mul_zero_zero B hB0
            rw [h00]
          have hMdet : M.det ≠ 0 := by
            have hprod : B 0 0 * M.det ≠ 0 := hblock ▸ hDdet
            exact (mul_ne_zero_iff.mp hprod).2
          obtain ⟨childFactors, hchild⟩ := lupDecomposeWithCost_nonsingular M hMdet
          refine ⟨assembleLUPFactors B eliminated.value (Equiv.swap 0 p.1) childFactors, ?_⟩
          simp [lupDecomposeWithCost, hpivot, B, eliminated, M, hchild]

/-- A successful execution certifies nonsingularity; a singular matrix cannot
pass every nonzero-pivot stage. -/
theorem lupDecomposeWithCost_success_det_ne_zero : ∀ {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) (factors : LUPFactors n F),
    (lupDecomposeWithCost n A).result = some factors → A.det ≠ 0
  | 0, _A, _factors, _hresult => by simp
  | n + 1, A, factors, hresult => by
      cases hpivot : (findPivotWithCost A).pivot with
      | none =>
          simp [lupDecomposeWithCost, hpivot] at hresult
      | some p =>
          let B := pivotedMatrix A p.1
          have hB0 : B 0 0 ≠ 0 := by
            simpa [B, pivotedMatrix] using p.2
          let eliminated := eliminateWithCost B hB0
          let M : Matrix (Fin n) (Fin n) F :=
            fun i j => eliminated.value (Fin.succ i) (Fin.succ j)
          let child := lupDecomposeWithCost n M
          cases hchild : child.result with
          | none =>
              have hchild' : (lupDecomposeWithCost n M).result = none := by
                simpa [child] using hchild
              simp [lupDecomposeWithCost, hpivot, B, eliminated, M, hchild'] at hresult
          | some childFactors =>
              have hchild' :
                  (lupDecomposeWithCost n M).result = some childFactors := by
                simpa [child] using hchild
              have hMdet : M.det ≠ 0 :=
                lupDecomposeWithCost_success_det_ne_zero M childFactors hchild'
              have hDcol : ∀ i : Fin n, eliminated.value (Fin.succ i) 0 = 0 :=
                eliminateWithCost_col_zero B hB0
              have hblock : eliminated.value.det = B 0 0 * M.det := by
                rw [det_block_schur eliminated.value hDcol]
                have h00 : eliminated.value 0 0 = B 0 0 := by
                  rw [eliminateWithCost_value]
                  exact elimination_mul_zero_zero B hB0
                rw [h00]
              have hDdet : eliminated.value.det ≠ 0 := by
                rw [hblock]
                exact mul_ne_zero hB0 hMdet
              have hBdet : B.det ≠ 0 := by
                rw [eliminateWithCost_value, Matrix.det_mul] at hDdet
                rw [det_unitLowerTriangular (elimination_unitLowerTriangular B hB0)] at hDdet
                simpa using hDdet
              have hdetEq : B.det =
                  ((Equiv.swap 0 p.1).permMatrix F).det * A.det := by
                dsimp [B]
                rw [pivotedMatrix_eq_permMatrix_mul, Matrix.det_mul]
              have hprod : ((Equiv.swap 0 p.1).permMatrix F).det * A.det ≠ 0 :=
                hdetEq ▸ hBdet
              exact (mul_ne_zero_iff.mp hprod).2

/-- Every successful execution has nonzero upper-triangular diagonal entries,
as required by backward substitution. -/
theorem lupDecomposeWithCost_upper_diag_ne_zero {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) (factors : LUPFactors n F)
    (hresult : (lupDecomposeWithCost n A).result = some factors) :
    ∀ i : Fin n, factors.upper i i ≠ 0 := by
  have hcorrect := lupDecomposeWithCost_sound A factors hresult
  have hA := lupDecomposeWithCost_success_det_ne_zero A factors hresult
  have hUdet := det_ne_zero_of_lup hcorrect.2.2 hcorrect.1 hA
  exact upperTriangular_diag_ne_zero_of_det_ne_zero factors.upper hcorrect.2.1 hUdet

/-- The total execution returns failure exactly for singular matrices. -/
theorem lupDecomposeWithCost_eq_none_iff {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) :
    (lupDecomposeWithCost n A).result = none ↔ A.det = 0 := by
  constructor
  · intro hnone
    by_contra hdet
    obtain ⟨factors, hsome⟩ := lupDecomposeWithCost_nonsingular A hdet
    rw [hnone] at hsome
    simp at hsome
  · intro hdet
    cases hresult : (lupDecomposeWithCost n A).result with
    | none => rfl
    | some factors =>
        exact False.elim
          ((lupDecomposeWithCost_success_det_ne_zero A factors hresult) hdet)

end Chapter28
end CLRS
