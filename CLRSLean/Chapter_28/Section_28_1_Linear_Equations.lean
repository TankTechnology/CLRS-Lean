import Mathlib

/-!
# 28.1 Solving systems of linear equations

This section formalizes the **LUP decomposition** (CLRS Theorem 28.1): every
nonsingular matrix {lit}`A` over a field admits a factorization
{lit}`P·A = L·U` where {lit}`P` is a permutation matrix, {lit}`L` is unit
lower-triangular, and {lit}`U` is upper-triangular.  The decomposition
underlies Gaussian elimination, the determinant, and matrix inversion.

Main results:

- Theorem {lit}`exists_lup_decomposition`: every nonsingular matrix admits an
  LUP decomposition `σ.permMatrix · A = L · U`.  The proof is by induction on
  `n`: the pivot row is swapped into row 0, one Gaussian-elimination step
  ({lit}`elimination`) zeroes the subdiagonal, the induction hypothesis is
  applied to the nonsingular Schur complement (nonsingularity via
  {lit}`det_block_schur`), and the block factors are assembled with the
  {lit}`finOneSumFin` reindexing.  Supporting lemmas cover pivot selection
  ({lit}`exists_col_zero_ne_zero`), the elimination step
  ({lit}`elimination_unitLowerTriangular` / {lit}`elimination_mul_zero_zero` /
  {lit}`elimination_mul_col_zero`), the unit-triangular determinant
  ({lit}`det_unitLowerTriangular`), and the permutation-matrix bookkeeping
  ({lit}`fromBlocks_one_zero_zero_permMatrix` / {lit}`conjPermMatrix`).
- Theorem {lit}`lup_solve_correct` (CLRS §28.1, Algorithm LUP-SOLVE): if
  {lit}`σ.permMatrix · A = L · U` is an LUP decomposition and the substitution
  equations {lit}`L·y = σ.permMatrix·b` and {lit}`U·x = y` hold, then
  {lit}`A·x = b` — forward then backward substitution through the factors
  solves the system.
- Theorem {lit}`forwardSubst_spec` (CLRS Lemma 28.1): `forwardSubst L b`,
  forward substitution through a unit lower-triangular `L`, satisfies
  {lit}`L·(forwardSubst L b) = b`.
- Theorem {lit}`backSubst_spec` (CLRS Lemma 28.2): `backSubst U y`, backward
  substitution through an upper-triangular `U` with nonzero diagonal,
  satisfies {lit}`U·(backSubst U y) = y`.
- Theorem {lit}`lupSolve_correct`: the constructive solver `lupSolve σ L U b`
  (forward-then-back substitution through the factors) solves {lit}`A·x = b`
  given an LUP decomposition of `A`.
- Theorem {lit}`exists_solution_of_nonsingular`: a nonsingular matrix over a
  field solves every linear system ({lit}`∃ x, A·x = b`).
- Theorems {lit}`unique_solution_of_nonsingular`,
  {lit}`unique_solution_unitLowerTriangular` (Lemma 28.1), and
  {lit}`unique_solution_upperTriangular` (Lemma 28.2): nonsingular,
  unit-lower-triangular, and upper-triangular systems with nonzero diagonal
  have at most one solution.

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
def elimination {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (_h : B 0 0 ≠ 0) :
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

/-- The block-diagonal matrix `diag(1, P₁)` with a `1 × 1` top-left block is the
permutation matrix of the sum-of-permutations `sumCongr 1 σ₁`. -/
lemma fromBlocks_one_zero_zero_permMatrix {n : ℕ} (σ₁ : Equiv.Perm (Fin n)) :
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0 (σ₁.permMatrix F) =
      (Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) σ₁).permMatrix F := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Pi.single_apply, eq_comm]

/-- Conjugating a permutation by an equivalence reindexes its permutation matrix:
`(e.trans σ.trans e.symm).permMatrix = σ.permMatrix.reindex e.symm e.symm`. -/
lemma conjPermMatrix {m n : Type*} [DecidableEq m] [DecidableEq n] (e : m ≃ n)
    (σ : Equiv.Perm n) :
    Equiv.Perm.permMatrix F ((e.trans σ).trans e.symm) = (σ.permMatrix F).reindex e.symm e.symm := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_symm, Equiv.apply_eq_iff_eq_symm_apply]

set_option linter.unnecessarySimpa false in
/-- If `i < j` in `Fin (n + 1)` then `j` is not the zero row. -/
lemma ne_zero_of_lt_succ {n : ℕ} {i j : Fin (n + 1)} (hij : i < j) : j ≠ 0 := by
  intro hj0
  have hi0 : i < (0 : Fin (n + 1)) := by simpa [hj0] using hij
  have hi0v : i.val < 0 := by simpa using hi0
  exact (Nat.not_lt_zero i.val) hi0v

set_option linter.unnecessarySimpa false in
/-- If `j < i` in `Fin (n + 1)` then `i` is not the zero row. -/
lemma ne_zero_of_lt {n : ℕ} {i j : Fin (n + 1)} (hji : j < i) : i ≠ 0 := by
  intro hi0
  have hj0 : j < (0 : Fin (n + 1)) := by simpa [hi0] using hji
  have hj0v : j.val < 0 := by simpa using hj0
  exact (Nat.not_lt_zero j.val) hj0v

/--
**Theorem 28.1 (LUP decomposition).**  Every nonsingular `n × n` matrix `A` over a
field admits an LUP decomposition: a permutation `σ`, a unit lower-triangular `L`,
and an upper-triangular `U` such that `σ.permMatrix · A = L · U`.

The proof is by induction on `n`.  In the inductive step we pivot the first column
so the leading entry is nonzero, perform one Gaussian-elimination step to zero the
subdiagonal, apply the induction hypothesis to the Schur complement, and assemble
the resulting block matrices.
-/
theorem exists_lup_decomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) F),
      IsUnitLowerTriangular L ∧ IsUpperTriangular U ∧ σ.permMatrix F * A = L * U := by
  classical
  induction n with
  | zero =>
      refine ⟨1, 1, 1, ?_, ?_, ?_⟩
      · simp [IsUnitLowerTriangular, IsLowerTriangular]
      · simp [IsUpperTriangular]
      · simp
        ext i j
        exact Fin.elim0 i
  | succ n ih =>
      obtain ⟨p, hp⟩ := exists_col_zero_ne_zero hA
      let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
      let B : Matrix (Fin (n + 1)) (Fin (n + 1)) F := σ.permMatrix F * A
      have hB : B 0 0 ≠ 0 := by
        dsimp [B, σ]
        exact perm_mul_zero_zero_ne_zero hp
      let E : Matrix (Fin (n + 1)) (Fin (n + 1)) F := elimination B hB
      let D : Matrix (Fin (n + 1)) (Fin (n + 1)) F := E * B
      let M : Matrix (Fin n) (Fin n) F := fun i j => D (Fin.succ i) (Fin.succ j)
      have hDcol : ∀ i : Fin n, D (Fin.succ i) 0 = 0 := by
        intro i
        dsimp [D, E]
        exact elimination_mul_col_zero B hB i
      have hMdet : M.det ≠ 0 := by
        have hBdet : B.det ≠ 0 := by
          dsimp [B, σ]
          rw [Matrix.det_mul]
          have hrinv : (Equiv.swap 0 p)⁻¹.permMatrix F * (Equiv.swap 0 p).permMatrix F = 1 := by
            rw [← Matrix.permMatrix_mul]
            simp
          have hdetσ : ((Equiv.swap 0 p).permMatrix F).det ≠ 0 := by
            exact Matrix.det_ne_zero_of_left_inverse hrinv
          exact mul_ne_zero hdetσ hA
        have hDdet : D.det ≠ 0 := by
          dsimp [D, E]
          rw [Matrix.det_mul]
          rw [det_unitLowerTriangular (elimination_unitLowerTriangular B hB)]
          simpa using hBdet
        have hblock : D.det = B 0 0 * M.det := by
          dsimp [M, D, E]
          rw [det_block_schur (elimination B hB * B) hDcol]
          rw [elimination_mul_zero_zero B hB]
        have hprod : B 0 0 * M.det ≠ 0 := by
          exact hblock ▸ hDdet
        exact (mul_ne_zero_iff.mp hprod).2
      obtain ⟨σ₁, L₁, U₁, hL₁, hU₁, hMfac⟩ := ih M hMdet
      let re : Fin (n + 1) ≃ Fin 1 ⊕ Fin n := finOneSumFin n
      let α : Matrix (Fin 1) (Fin 1) F := fun _ _ => D 0 0
      let v : Matrix (Fin 1) (Fin n) F := fun _ j => D 0 (Fin.succ j)
      let mult : Matrix (Fin n) (Fin 1) F := fun i _ => -E (Fin.succ i) 0
      let P₁ : Matrix (Fin n) (Fin n) F := σ₁.permMatrix F
      let diagP : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
        (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 0 P₁).reindex re.symm re.symm
      let E' : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
        (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 mult
          (1 : Matrix (Fin n) (Fin n) F)).reindex re.symm re.symm
      let L : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
        (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) F) 0 (P₁ * mult) L₁).reindex re.symm re.symm
      let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
        (Matrix.fromBlocks α v (0 : Matrix (Fin n) (Fin 1) F) U₁).reindex re.symm re.symm
      let σP : Equiv.Perm (Fin (n + 1)) :=
        (re.trans (Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) σ₁)).trans re.symm
      let σ₀ : Equiv.Perm (Fin (n + 1)) := σ * σP
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
        dsimp [σP, diagP]
        rw [conjPermMatrix re (Equiv.Perm.sumCongr (1 : Equiv.Perm (Fin 1)) σ₁)]
        rw [← fromBlocks_one_zero_zero_permMatrix σ₁]
        dsimp [P₁]
      have hDiagE'D : diagP * E' * D = L * U := by
        apply (reindexRingEquiv F re).injective
        rw [map_mul, map_mul]
        rw [show (reindexRingEquiv F re) D = Matrix.fromBlocks α v (0 : Matrix (Fin n) (Fin 1) F) M by
          simpa using hDblocks]
        rw [map_mul]
        rw [show (reindexRingEquiv F re) diagP = Matrix.fromBlocks 1 0 0 P₁ by
          simp [diagP, Matrix.reindex_apply, Matrix.submatrix_submatrix]]
        rw [show (reindexRingEquiv F re) E' = Matrix.fromBlocks 1 0 mult
            (1 : Matrix (Fin n) (Fin n) F) by
          simp [E', Matrix.reindex_apply, Matrix.submatrix_submatrix]]
        rw [show (reindexRingEquiv F re) L = Matrix.fromBlocks 1 0 (P₁ * mult) L₁ by
          simp [L, Matrix.reindex_apply, Matrix.submatrix_submatrix]]
        rw [show (reindexRingEquiv F re) U = Matrix.fromBlocks α v (0 : Matrix (Fin n) (Fin 1) F) U₁ by
          simp [U, Matrix.reindex_apply, Matrix.submatrix_submatrix]]
        simp [Matrix.fromBlocks_multiply, P₁, hMfac]
      have hBD : B = E' * D := by
        calc
          B = 1 * B := by rw [one_mul]
          _ = (E' * E) * B := by rw [hEinv]
          _ = E' * (E * B) := by rw [Matrix.mul_assoc]
          _ = E' * D := by rfl
      have hDiagB : diagP * B = L * U := by
        calc
          diagP * B = diagP * (E' * D) := by rw [hBD]
          _ = (diagP * E') * D := by rw [Matrix.mul_assoc]
          _ = L * U := hDiagE'D
      have hEq : σ₀.permMatrix F * A = L * U := by
        calc
          σ₀.permMatrix F * A = (σ * σP).permMatrix F * A := by rfl
          _ = (σP.permMatrix F * σ.permMatrix F) * A := by rw [Matrix.permMatrix_mul]
          _ = σP.permMatrix F * (σ.permMatrix F * A) := by rw [Matrix.mul_assoc]
          _ = σP.permMatrix F * B := by rfl
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
              dsimp [re]
              simp [hi, finOneSumFin]
            have hrj : re j = Sum.inr (j.pred hj) := by
              dsimp [re]
              simp [hj, finOneSumFin]
            rw [hri, hrj]
            simp
          · have hj : j ≠ 0 := ne_zero_of_lt_succ hij
            dsimp only [L]
            rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
            have hri : re i = Sum.inr (i.pred hi) := by
              dsimp [re]
              simp [hi, finOneSumFin]
            have hrj : re j = Sum.inr (j.pred hj) := by
              dsimp [re]
              simp [hj, finOneSumFin]
            rw [hri, hrj]
            simp
            apply hL₁.1
            have hsi : i = Fin.succ (i.pred hi) := (Fin.succ_pred i hi).symm
            have hsj : j = Fin.succ (j.pred hj) := (Fin.succ_pred j hj).symm
            have hlt : Fin.succ (i.pred hi) < Fin.succ (j.pred hj) := by
              rw [hsi, hsj] at hij
              exact hij
            exact Fin.succ_lt_succ_iff.mp hlt
        · intro i
          by_cases hi : i = 0
          · dsimp only [L]
            rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
            have hri : re i = Sum.inl (⟨0, by omega⟩ : Fin 1) := by
              dsimp [re]
              simp [hi, finOneSumFin]
            rw [hri]
            simp
          · dsimp only [L]
            rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
            have hri : re i = Sum.inr (i.pred hi) := by
              dsimp [re]
              simp [hi, finOneSumFin]
            rw [hri]
            simp
            exact hL₁.2 (i.pred hi)
      have hU : IsUpperTriangular U := by
        intro i j hji
        by_cases hj : j = 0
        · have hi : i ≠ 0 := ne_zero_of_lt hji
          dsimp only [U]
          rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
          have hrj : re j = Sum.inl (⟨0, by omega⟩ : Fin 1) := by
            dsimp [re]
            simp [hj, finOneSumFin]
          have hri : re i = Sum.inr (i.pred hi) := by
            dsimp [re]
            simp [hi, finOneSumFin]
          rw [hrj, hri]
          simp
        · have hi : i ≠ 0 := ne_zero_of_lt hji
          dsimp only [U]
          rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
          have hrj : re j = Sum.inr (j.pred hj) := by
            dsimp [re]
            simp [hj, finOneSumFin]
          have hri : re i = Sum.inr (i.pred hi) := by
            dsimp [re]
            simp [hi, finOneSumFin]
          rw [hrj, hri]
          simp
          apply hU₁
          have hsj : j = Fin.succ (j.pred hj) := (Fin.succ_pred j hj).symm
          have hsi : i = Fin.succ (i.pred hi) := (Fin.succ_pred i hi).symm
          have hlt : Fin.succ (j.pred hj) < Fin.succ (i.pred hi) := by
            rw [hsj, hsi] at hji
            exact hji
          exact Fin.succ_lt_succ_iff.mp hlt
      exact ⟨σ₀, L, U, hL, hU, hEq⟩

/--
**LUP-SOLVE correctness (CLRS §28.1, Algorithm LUP-SOLVE).**  If
`σ.permMatrix · A = L · U` is an LUP decomposition and `y`, `x` are obtained by
forward and backward substitution (`L·y = σ.permMatrix·b`, `U·x = y`), then `x`
solves the linear system `A·x = b`.

The proof composes the two substitution equations through the factorization:
`σ.permMatrix·(A·x) = (σ.permMatrix·A)·x = (L·U)·x = L·(U·x) = L·y =
σ.permMatrix·b`, then cancels the permutation matrix `σ.permMatrix` (whose
`mulVec` is the bijection `v ↦ v∘σ`).
-/
theorem lup_solve_correct {n : ℕ} {A L U : Matrix (Fin n) (Fin n) F} {σ : Equiv.Perm (Fin n)}
    (hLUP : σ.permMatrix F * A = L * U) (b x y : Fin n → F)
    (hLy : L *ᵥ y = σ.permMatrix F *ᵥ b) (hUx : U *ᵥ x = y) :
    A *ᵥ x = b := by
  have hPAx : σ.permMatrix F *ᵥ (A *ᵥ x) = σ.permMatrix F *ᵥ b := by
    rw [Matrix.mulVec_mulVec]
    rw [hLUP]
    rw [← Matrix.mulVec_mulVec]
    rw [hUx]
    exact hLy
  have hcomp : (A *ᵥ x) ∘ σ = b ∘ σ := by
    rw [Matrix.permMatrix_mulVec, Matrix.permMatrix_mulVec] at hPAx
    exact hPAx
  have h := congrArg (fun f : Fin n → F => f ∘ σ.symm) hcomp
  simpa [Function.comp_assoc] using h

/-- A nonsingular matrix over a field solves every linear system: if
`A.det ≠ 0` then for every right-hand side `b` there is `x` with `A·x = b`. -/
theorem exists_solution_of_nonsingular {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0)
    (b : Fin n → F) : ∃ x : Fin n → F, A *ᵥ x = b := by
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hA
  exact Matrix.mulVec_surjective_iff_isUnit.2 hunit b

/--
**Forward substitution (CLRS Lemma 28.1).**  `forwardSubst L b` is the vector
`y` computed by forward substitution through the unit lower-triangular matrix
`L`; the recursion splits off the first component `y₀ = b₀` and substitutes the
tail through the trailing block `L₂`.

The constructor `forwardSubst` is total (any `L`); its correctness
({lit}`forwardSubst_spec`) requires `L` to be unit lower-triangular.
-/
noncomputable def forwardSubst : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F)
  | 0, _, _ => fun i => Fin.elim0 i
  | n + 1, L, b =>
      let L2 : Matrix (Fin n) (Fin n) F := fun i j => L (Fin.succ i) (Fin.succ j)
      Fin.cons (b 0) (forwardSubst L2 (fun i => b (Fin.succ i) - L (Fin.succ i) 0 * b 0))

/-- The trailing block of a unit lower-triangular matrix is unit lower-triangular. -/
lemma unitLowerTriangular_tail {n : ℕ} (L : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hL : IsUnitLowerTriangular L) :
    IsUnitLowerTriangular (fun i j : Fin n => L (Fin.succ i) (Fin.succ j)) := by
  constructor
  · intro i j hij
    exact hL.1 (Fin.succ_lt_succ_iff.mpr hij)
  · intro i
    exact hL.2 (Fin.succ i)

/--
**Forward substitution solves `L·y = b` (CLRS Lemma 28.1).**  For a unit
lower-triangular `L`, `forwardSubst L b` satisfies `L·(forwardSubst L b) = b`.
-/
theorem forwardSubst_spec : ∀ {n : ℕ} (L : Matrix (Fin n) (Fin n) F) (b : Fin n → F),
    IsUnitLowerTriangular L → L *ᵥ forwardSubst L b = b
  | 0, _, _, _ => by
      ext i
      exact Fin.elim0 i
  | n + 1, L, b, hL =>
      by
      let L2 : Matrix (Fin n) (Fin n) F := fun i j => L (Fin.succ i) (Fin.succ j)
      let b2 : Fin n → F := fun i => b (Fin.succ i) - L (Fin.succ i) 0 * b 0
      have hL2 : IsUnitLowerTriangular L2 := by
        simpa [L2] using (unitLowerTriangular_tail L hL)
      have hspec : L2 *ᵥ forwardSubst L2 b2 = b2 := forwardSubst_spec L2 b2 hL2
      change L *ᵥ Fin.cons (b 0) (forwardSubst L2 b2) = b
      ext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · unfold Matrix.mulVec dotProduct
        rw [Fin.sum_univ_succ]
        have h00 : L 0 0 = 1 := hL.2 0
        have h0k : ∀ k : Fin n, L 0 (Fin.succ k) = 0 := fun k => hL.1 (Fin.succ_pos k)
        simp [Fin.cons_zero, Fin.cons_succ, h00, h0k]
      · unfold Matrix.mulVec dotProduct
        rw [Fin.sum_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
        change L (Fin.succ i') 0 * b 0 + (L2 *ᵥ forwardSubst L2 b2) i' = b (Fin.succ i')
        rw [hspec]
        simp [b2]

/--
**Backward substitution (CLRS Lemma 28.2).**  `backSubst U y` is the vector
`x` computed by backward substitution through the upper-triangular matrix `U`;
the recursion splits off the last component `xₙ = yₙ/Uₙₙ` and substitutes the
tail through the leading block `U₁`.

The constructor `backSubst` is total (any `U`); its correctness
({lit}`backSubst_spec`) requires `U` to be upper-triangular with nonzero
diagonal.
-/
noncomputable def backSubst : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) F → (Fin n → F) → (Fin n → F)
  | 0, _, _ => fun i => Fin.elim0 i
  | n + 1, U, y =>
      let last : Fin (n + 1) := Fin.last n
      let U1 : Matrix (Fin n) (Fin n) F := fun i j => U (Fin.castSucc i) (Fin.castSucc j)
      let xl : F := y last / U last last
      Fin.snoc (backSubst U1 (fun i => y (Fin.castSucc i) - U (Fin.castSucc i) last * xl)) xl

/-- The leading block of an upper-triangular matrix is upper-triangular. -/
lemma upperTriangular_tail {n : ℕ} (U : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hU : IsUpperTriangular U) :
    IsUpperTriangular (fun i j : Fin n => U (Fin.castSucc i) (Fin.castSucc j)) := by
  intro i j hji
  exact hU (Fin.castSucc_lt_castSucc_iff.mpr hji)

/--
**Backward substitution solves `U·x = y` (CLRS Lemma 28.2).**  For an
upper-triangular `U` with nonzero diagonal, `backSubst U y` satisfies
`U·(backSubst U y) = y`.
-/
theorem backSubst_spec : ∀ {n : ℕ} (U : Matrix (Fin n) (Fin n) F) (y : Fin n → F),
    IsUpperTriangular U → (∀ i : Fin n, U i i ≠ 0) → U *ᵥ backSubst U y = y
  | 0, _, _, _, _ => by ext i; exact Fin.elim0 i
  | n + 1, U, y, hU, hdiag =>
      by
      let last : Fin (n + 1) := Fin.last n
      let U1 : Matrix (Fin n) (Fin n) F := fun i j => U (Fin.castSucc i) (Fin.castSucc j)
      let xl : F := y last / U last last
      let y1 : Fin n → F := fun i => y (Fin.castSucc i) - U (Fin.castSucc i) last * xl
      have hU1 : IsUpperTriangular U1 := by
        simpa [U1] using (upperTriangular_tail U hU)
      have hdiag1 : ∀ i : Fin n, U1 i i ≠ 0 := by
        intro i
        exact hdiag (Fin.castSucc i)
      have hspec : U1 *ᵥ backSubst U1 y1 = y1 := backSubst_spec U1 y1 hU1 hdiag1
      change U *ᵥ Fin.snoc (backSubst U1 y1) xl = y
      ext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · unfold Matrix.mulVec dotProduct
        rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc_castSucc, Fin.snoc_last]
        change (U1 *ᵥ backSubst U1 y1) i' + U (Fin.castSucc i') last * xl = y (Fin.castSucc i')
        rw [hspec]
        simp [y1]
      · unfold Matrix.mulVec dotProduct
        rw [Fin.sum_univ_castSucc]
        have hUlast : ∀ j' : Fin n, U last (Fin.castSucc j') = 0 := by
          intro j'
          exact hU (Fin.castSucc_lt_last j')
        simp [Fin.snoc_castSucc, Fin.snoc_last]
        have hz : (∑ x : Fin n, U (Fin.last n) (Fin.castSucc x) * backSubst U1 y1 x) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro x hx
          have h0 : U (Fin.last n) (Fin.castSucc x) = 0 := hU (Fin.castSucc_lt_last x)
          simp [h0]
        rw [hz]
        simp [xl]
        have hln : U last last ≠ 0 := hdiag last
        field_simp [hln]
        ring

/--
**LUP-SOLVE.**  `lupSolve σ L U b` solves `A·x = b` through an LUP
decomposition `σ.permMatrix · A = L · U` by forward-substituting
`L·y = σ.permMatrix·b` and then back-substituting `U·x = y`.  It is the
constructive counterpart of the compositional theorem `lup_solve_correct`.
-/
noncomputable def lupSolve {n : ℕ} (σ : Equiv.Perm (Fin n)) (L U : Matrix (Fin n) (Fin n) F)
    (b : Fin n → F) : Fin n → F :=
  backSubst U (forwardSubst L (σ.permMatrix F *ᵥ b))

/-- **LUP-SOLVE correctness.**  If `σ.permMatrix · A = L · U` is an LUP
decomposition with `L` unit lower-triangular and `U` upper-triangular with
nonzero diagonal, then `lupSolve σ L U b` solves `A·x = b`. -/
theorem lupSolve_correct {n : ℕ} {A L U : Matrix (Fin n) (Fin n) F} {σ : Equiv.Perm (Fin n)}
    (hLUP : σ.permMatrix F * A = L * U) (hL : IsUnitLowerTriangular L)
    (hU : IsUpperTriangular U) (hUdiag : ∀ i : Fin n, U i i ≠ 0) (b : Fin n → F) :
    A *ᵥ lupSolve σ L U b = b := by
  unfold lupSolve
  let Pb : Fin n → F := σ.permMatrix F *ᵥ b
  let y : Fin n → F := forwardSubst L Pb
  have hLy : L *ᵥ y = σ.permMatrix F *ᵥ b := by
    simpa [y, Pb] using (forwardSubst_spec L Pb hL)
  have hUx : U *ᵥ (backSubst U y) = y := by
    exact backSubst_spec U y hU hUdiag
  exact lup_solve_correct hLUP b (backSubst U y) y hLy hUx

/-- A nonsingular matrix over a field has a unique solution for every linear
system: if `A·x₁ = b` and `A·x₂ = b` then `x₁ = x₂`. -/
theorem unique_solution_of_nonsingular {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0)
    (b x1 x2 : Fin n → F) (h1 : A *ᵥ x1 = b) (h2 : A *ᵥ x2 = b) : x1 = x2 := by
  have hunit : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hA
  apply (Matrix.mulVec_injective_iff_isUnit.2 hunit)
  calc
    A *ᵥ x1 = b := h1
    _ = A *ᵥ x2 := h2.symm

/-- A unit lower-triangular system `L·x = b` has at most one solution
(CLRS Lemma 28.1: forward substitution computes the unique one). -/
theorem unique_solution_unitLowerTriangular {n : ℕ} (L : Matrix (Fin n) (Fin n) F)
    (hL : IsUnitLowerTriangular L) (b x1 x2 : Fin n → F)
    (h1 : L *ᵥ x1 = b) (h2 : L *ᵥ x2 = b) : x1 = x2 := by
  have hunit : IsUnit L := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [det_unitLowerTriangular hL]
    exact isUnit_one
  apply (Matrix.mulVec_injective_iff_isUnit.2 hunit)
  calc
    L *ᵥ x1 = b := h1
    _ = L *ᵥ x2 := h2.symm

/-- An upper-triangular system `U·x = y` with nonzero diagonal has at most one
solution (CLRS Lemma 28.2: backward substitution computes the unique one). -/
theorem unique_solution_upperTriangular {n : ℕ} (U : Matrix (Fin n) (Fin n) F)
    (hU : IsUpperTriangular U) (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (y x1 x2 : Fin n → F) (h1 : U *ᵥ x1 = y) (h2 : U *ᵥ x2 = y) : x1 = x2 := by
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular]
    · exact Finset.prod_ne_zero_iff.2 (fun i hi => hdiag i)
    · intro i j hij
      exact hU hij
  have hunit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  apply (Matrix.mulVec_injective_iff_isUnit.2 hunit)
  calc
    U *ᵥ x1 = y := h1
    _ = U *ᵥ x2 := h2.symm

end Chapter28

end CLRS
