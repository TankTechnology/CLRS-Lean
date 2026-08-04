import Mathlib

/-!
# 28.1 Solving systems of linear equations

This section formalizes the **LUP decomposition** (CLRS Theorem 28.1): every
nonsingular matrix {lit}`A` over a field admits a factorization
{lit}`P·A = L·U` where {lit}`P` is a permutation matrix, {lit}`L` is unit
lower-triangular, and {lit}`U` is upper-triangular.  The decomposition
underlies Gaussian elimination, the determinant, and matrix inversion.

Main results:

- Theorem {lit}`exists_lup_decomposition`: the LUP decomposition existence.

Notation conventions:

- {lit}`A` : an {lit}`n × n` matrix over a field {lit}`F`.
- {lit}`σ.permMatrix F` : the permutation matrix of {lit}`σ`.
- {lit}`IsUpperTriangular` / {lit}`IsLowerTriangular`: zero above/below the
  main diagonal.
- {lit}`IsUnitLowerTriangular`: lower-triangular with diagonal ones.
-/

namespace CLRS

namespace Chapter28

open Matrix

variable {F : Type} [Field F]

/-- Upper-triangular: every entry strictly below the main diagonal is zero. -/
def IsUpperTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ ⦃i j : Fin n⦄, j < i → M i j = 0

/-- Lower-triangular: every entry strictly above the main diagonal is zero. -/
def IsLowerTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j → M i j = 0

/-- Unit lower-triangular: lower-triangular with every diagonal entry equal to
one (the shape of the {lit}`L` factor in an LUP decomposition). -/
def IsUnitLowerTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  IsLowerTriangular M ∧ ∀ i : Fin n, M i i = 1

/-- The determinant of a matrix with an all-zero column is zero. -/
lemma det_eq_zero_of_col_zero {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    (h : ∀ i : Fin (n + 1), A i 0 = 0) : A.det = 0 := by
  classical
  -- det A = Σ σ, sign σ · ∏ i, A (σ i) i; column 0 zero kills every term.
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  have hfactor : A (σ 0) 0 = 0 := h (σ 0)
  have hprod : (∏ i : Fin (n + 1), A (σ i) i) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ _) hfactor
  simp [hprod]

/-- A nonsingular matrix has a nonzero entry in its first column (a pivot). -/
lemma exists_col_zero_ne_zero {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    (hA : A.det ≠ 0) : ∃ p : Fin (n + 1), A p 0 ≠ 0 := by
  classical
  by_contra h
  have hzero : ∀ i : Fin (n + 1), A i 0 = 0 := by
    intro i
    exact not_ne_iff.mp (fun hne => h ⟨i, hne⟩)
  exact hA (det_eq_zero_of_col_zero hzero)

/-- Multiplying by a permutation matrix on the left permutes the rows:
`(σ.permMatrix * A) i j = A (σ i) j`. -/
lemma permMatrix_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (σ.permMatrix F * A) i j = A (σ i) j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp
  · intro b hb hbne
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hbne.symm]
  · simp

/-- Swapping the pivot row `p` into row `0` makes the leading entry nonzero:
`(swap 0 p).permMatrix * A` has a nonzero `(0,0)` entry. -/
lemma perm_mul_zero_zero_ne_zero {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    {p : Fin (n + 1)} (hp : A p 0 ≠ 0) :
    ((Equiv.swap 0 p).permMatrix F * A) 0 0 ≠ 0 := by
  have h : ((Equiv.swap 0 p).permMatrix F * A) 0 0 = A p 0 := by
    rw [permMatrix_mul_apply]
    simp
  rw [h]
  exact hp

/-- The Gaussian-elimination step matrix: unit lower-triangular, with the
subdiagonal entries of column `0` chosen to zero them out in `E * B`. -/
def elimination {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  fun i j => if i = j then 1 else if j = 0 then -B i 0 / B 0 0 else 0

/-- The elimination matrix is unit lower-triangular. -/
lemma elimination_unitLowerTriangular {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (h : B 0 0 ≠ 0) : IsUnitLowerTriangular (elimination B h) := by
  constructor
  · intro i j hij
    unfold elimination
    by_cases hEq : i = j
    · exfalso; exact (ne_of_lt hij) hEq
    · have hj0 : j ≠ 0 := by
        intro hj
        exact (not_lt_of_ge (by simp [hj]) (hij : i < j))
      simp [hEq, hj0]
  · intro i
    unfold elimination
    simp

/-- The pivot entry `(0,0)` is unchanged by the elimination step. -/
lemma elimination_mul_zero_zero {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (h : B 0 0 ≠ 0) : (elimination B h * B) 0 0 = B 0 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · unfold elimination
    simp
  · intro b hb hb0
    unfold elimination
    by_cases hEq : (0 : Fin (n + 1)) = b
    · exfalso; exact hb0 hEq.symm
    · have hb0' : b ≠ (0 : Fin (n + 1)) := by
        intro hb'
        exact hEq hb'.symm
      simp [hEq, hb0']
  · simp

/-- The elimination step zeroes out column `0` below the pivot. -/
lemma elimination_mul_col_zero {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (h : B 0 0 ≠ 0) (i : Fin n) : (elimination B h * B) (Fin.succ i) 0 = 0 := by
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin (n + 1), k ≠ Fin.succ i → k ≠ 0 →
      elimination B h (Fin.succ i) k * B k 0 = 0 := by
    intro k hk1 hk0
    unfold elimination
    have hne : Fin.succ i ≠ k := by exact Ne.symm hk1
    simp [hne, hk0]
  have hself : elimination B h (Fin.succ i) (Fin.succ i) * B (Fin.succ i) 0 =
      B (Fin.succ i) 0 := by
    unfold elimination
    simp
  have hzero : elimination B h (Fin.succ i) 0 * B 0 0 =
      (-B (Fin.succ i) 0 / B 0 0) * B 0 0 := by
    unfold elimination
    simp
  let S : Finset (Fin (n + 1)) := ({Fin.succ i, 0} : Finset (Fin (n + 1)))
  have hsubset : S ⊆ Finset.univ := by intro k hk; simp
  have hsubsum : (∑ k ∈ S, elimination B h (Fin.succ i) k * B k 0) =
      (∑ k : Fin (n + 1), elimination B h (Fin.succ i) k * B k 0) := by
    refine Finset.sum_subset hsubset ?_
    intro k hk hnot
    have hneq : ¬ k = Fin.succ i ∧ ¬ k = 0 := not_or.mp (by simpa [S] using hnot)
    exact hterm k hneq.1 hneq.2
  have hS : (∑ k ∈ S, elimination B h (Fin.succ i) k * B k 0) =
      B (Fin.succ i) 0 + (-B (Fin.succ i) 0 / B 0 0) * B 0 0 := by
    have hpair : ({Fin.succ i, 0} : Finset (Fin (n + 1))) =
        insert (Fin.succ i) ({0} : Finset (Fin (n + 1))) := by
      ext k
      simp [Finset.mem_insert]
    dsimp [S]
    rw [hpair]
    rw [Finset.sum_insert (by simp)]
    rw [Finset.sum_singleton]
    rw [hself, hzero]
  have hsum : (∑ k : Fin (n + 1), elimination B h (Fin.succ i) k * B k 0) =
      B (Fin.succ i) 0 + (-B (Fin.succ i) 0 / B 0 0) * B 0 0 := by
    rw [← hsubsum]
    exact hS
  rw [hsum]
  field_simp [h]
  ring

/-- A permutation of `Fin n` other than the identity sends some index strictly
below itself (so the identity is the only `≤`-monotone bijection). -/
lemma exists_lt_of_perm_ne_id {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    ∃ i : Fin n, σ i < i := by
  classical
  by_contra h
  have hle : ∀ i : Fin n, i ≤ σ i := by
    intro i
    exact le_of_not_gt (fun hgt => h ⟨i, hgt⟩)
  have hsum : (∑ i : Fin n, (σ i).val) = ∑ i : Fin n, i.val := by
    simpa using (Equiv.sum_comp σ (fun i : Fin n => i.val))
  by_cases hall : ∀ i : Fin n, σ i = i
  · exact hσ (Equiv.ext (fun i => hall i))
  · rcases not_forall.mp hall with ⟨i, hne⟩
    have hgt : i < σ i := lt_of_le_of_ne (hle i) (Ne.symm hne)
    have hlt : (∑ i : Fin n, i.val) < (∑ i : Fin n, (σ i).val) := by
      exact Finset.sum_lt_sum (fun j hj => hle j) ⟨i, by simp, hgt⟩
    exact (not_lt_of_ge (le_of_eq hsum)) hlt



/-- A unit lower-triangular matrix has determinant one: in the expansion, every
non-identity permutation `σ` picks a factor `M (σ i) i` with `σ i < i`, which
is zero. -/
lemma det_unitLowerTriangular {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : IsUnitLowerTriangular M) : M.det = 1 := by
  classical
  rw [Matrix.det_apply]
  have hId : Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) • ∏ i : Fin n, M i i = 1 := by
    simp [hM.2]
  have hone : ∀ σ : Equiv.Perm (Fin n), σ ≠ 1 →
      Equiv.Perm.sign σ • ∏ i : Fin n, M (σ i) i = 0 := by
    intro σ hσ
    rcases exists_lt_of_perm_ne_id hσ with ⟨i, hi⟩
    have hzero : M (σ i) i = 0 := hM.1 hi
    have hprod : (∏ i : Fin n, M (σ i) i) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [hprod]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simpa using hId
  · intro σ hσ hne
    exact hone σ hne
  · intro hσ1
    exfalso
    exact hσ1 (by simp)

/-- Reindex `Fin (n + 1)` as `Fin 1 ⊕ Fin n`: row `0 ↦ inl ()`, row `succ i ↦ inr i`.
This is the bookkeeping that lets an `(n + 1) × (n + 1)` matrix be viewed as a
`2 × 2` block matrix with a `1 × 1` top-left block. -/
noncomputable def finOneSumFin (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n where
  toFun i := if h : i = 0 then Sum.inl ⟨0, by omega⟩ else Sum.inr (i.pred h)
  invFun x := Sum.elim (fun _ => (0 : Fin (n + 1))) Fin.succ x
  left_inv := by
    intro i
    by_cases h : i = 0
    · simp [h]
    · simp [h]
  right_inv := by
    intro x
    cases x with
    | inl j =>
        have hj : (⟨0, by omega⟩ : Fin 1) = j := by
          ext
          omega
        simp [hj]
    | inr i =>
        simp

@[simp]
lemma finOneSumFin_symm_inl (n : ℕ) (j : Fin 1) :
    (finOneSumFin n).symm (Sum.inl j) = (0 : Fin (n + 1)) := by
  rfl

@[simp]
lemma finOneSumFin_symm_inr (n : ℕ) (i : Fin n) :
    (finOneSumFin n).symm (Sum.inr i) = Fin.succ i := by
  rfl

/-- The determinant of a 1×1 matrix is its single entry. -/
lemma det_const_fin_one (x : F) : Matrix.det (fun _ _ : Fin 1 => x) = x := by
  simp

/-- The determinant of a block-lower-triangular matrix: if the first column of `C`
below the pivot is all zero, then `det C = C 0 0 · det M` where `M` is the Schur
complement (the `succ`/`succ` submatrix).  This is the `n + 1` case of CLRS
Lemma 28.1's determinant step. -/
lemma det_block_schur {n : ℕ} (C : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (h : ∀ i : Fin n, C (Fin.succ i) 0 = 0) :
    C.det = C 0 0 * Matrix.det (fun i j : Fin n => C (Fin.succ i) (Fin.succ j)) := by
  classical
  let e : Fin (n + 1) ≃ Fin 1 ⊕ Fin n := finOneSumFin n
  let C' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) F := C.reindex e e
  have hdet : C'.det = C.det := by
    simp [C']
  have h21 : C'.toBlocks₂₁ = 0 := by
    ext i j
    simp [C', Matrix.reindex_apply, e, Matrix.toBlocks₂₁]
    exact h i
  have h11 : C'.toBlocks₁₁ = (fun _ _ : Fin 1 => C 0 0) := by
    ext i j
    simp [C', Matrix.reindex_apply, e, Matrix.toBlocks₁₁]
  have h22 : C'.toBlocks₂₂ = (fun i j : Fin n => C (Fin.succ i) (Fin.succ j)) := by
    ext i j
    simp [C', Matrix.reindex_apply, e, Matrix.toBlocks₂₂]
  calc
    C.det = C'.det := by rw [hdet]
    _ = (Matrix.fromBlocks C'.toBlocks₁₁ C'.toBlocks₁₂ C'.toBlocks₂₁ C'.toBlocks₂₂).det := by
      rw [Matrix.fromBlocks_toBlocks]
    _ = C'.toBlocks₁₁.det * C'.toBlocks₂₂.det := by
      rw [h21]
      rw [Matrix.det_fromBlocks_zero₂₁]
    _ = C 0 0 * Matrix.det (fun i j : Fin n => C (Fin.succ i) (Fin.succ j)) := by
      rw [h11, h22]
      rw [det_const_fin_one]

end Chapter28

end CLRS
