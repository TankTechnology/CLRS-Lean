import CLRSLean.Chapter_28.Section_28_1_Linear_Equations

/-!
# 28.3 Symmetric positive-definite matrices and least-squares approximation

This section formalizes CLRS §28.3: symmetric positive-definite (SPD) matrices,
the Cholesky decomposition (Theorem 28.3), and least-squares approximation via
the normal equations (Theorem 28.4).

Main results:

- Definition {lit}`IsSymPosDef`: a real matrix is SPD if it is symmetric and
  {lit}`xᵀAx > 0` for every nonzero vector {lit}`x`.
- Theorem {lit}`isSymPosDef_iff_posDef`: SPD coincides with Mathlib's
  {lit}`Matrix.PosDef`, giving nonsingularity ({lit}`IsSymPosDef.det_pos`),
  positive diagonal ({lit}`IsSymPosDef.diag_pos`), and injectivity of
  {lit}`mulVec` ({lit}`IsSymPosDef.mulVec_injective`).
- Theorem {lit}`posDef_mul_transpose`: if {lit}`A` has full column rank, then
  {lit}`AᵀA` is SPD (the Gram matrix is nonsingular).
- Theorem {lit}`cholesky_decomposition` (Theorem 28.3): every SPD matrix factors
  as {lit}`A = L·Lᵀ` with {lit}`L` lower-triangular with positive diagonal
  ({lit}`IsLowerTriangularPosDiag`).  The recursive construction uses the block
  factor {lit}`L = [[√a, 0],[v/√a, L₂]]` ({lit}`choleskyFactor`) with the
  positive-definite Schur complement ({lit}`cholesky_schur_complement`).
- Theorem {lit}`normal_equations_minimizes` (Theorem 28.4): if {lit}`xh`
  satisfies the normal equations {lit}`Aᵀ(A·xh - b) = 0`, then {lit}`xh`
  minimizes the squared residual {lit}`(A·x - b)⬝ᵥ(A·x - b)`.
- Theorem {lit}`normal_equations_unique`: when {lit}`A` has full column rank the
  minimizer is unique.
- Theorem {lit}`least_squares_closed_form`: {lit}`xh = (AᵀA)⁻¹·(Aᵀ·b)` satisfies
  the normal equations — the closed-form least-squares solution.

This section now covers the whole of CLRS §28.3: the SPD foundations, the
Cholesky decomposition (Theorem 28.3), and least-squares approximation
(Theorem 28.4).

Notation conventions:

- {lit}`A` : an {lit}`m × n` matrix over the reals; in the SPD sections,
  an {lit}`n × n` matrix.
- {lit}`v ⬝ᵥ w` : the Euclidean dot product {lit}`∑ᵢ vᵢwᵢ`; over the reals
  {lit}`v ⬝ᵥ v` is the squared 2-norm {lit}`‖v‖₂²`.
- {lit}`A *ᵥ x` : matrix-vector product.
-/

namespace CLRS

namespace Chapter28

open Matrix

section SymPosDef

/-- A real matrix is **symmetric positive-definite** (SPD) when it is symmetric
and `xᵀAx > 0` for every nonzero vector `x` (CLRS §28.3).  This is the CLRS
definition; `isSymPosDef_iff_posDef` shows it coincides with Mathlib's
`Matrix.PosDef`. -/
def IsSymPosDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

/-- The CLRS notion of symmetric positive-definite coincides with Mathlib's
`Matrix.PosDef` (Hermitian with `xᴴAx > 0`); over the reals `xᴴ = x` and
Hermitian means symmetric. -/
theorem isSymPosDef_iff_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} :
    IsSymPosDef A ↔ A.PosDef := by
  constructor
  · intro hA
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · simpa using hA.1
    · intro x hx
      exact hA.2 x hx
  · intro hA
    constructor
    · exact Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
    · intro x hx
      simpa using hA.dotProduct_mulVec_pos hx

namespace IsSymPosDef

/-- An SPD matrix is symmetric. -/
theorem isSymm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) : A.IsSymm :=
  hA.1

/-- An SPD matrix satisfies `xᵀAx > 0` for every nonzero `x`. -/
theorem dotProduct_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A)
    {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ (A *ᵥ x) :=
  hA.2 x hx

/-- An SPD matrix is positive definite in the Mathlib sense. -/
theorem posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) : A.PosDef :=
  isSymPosDef_iff_posDef.mp hA

/-- **SPD matrices are nonsingular**: the determinant is positive. -/
theorem det_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) : 0 < A.det := by
  exact hA.posDef.det_pos

/-- An SPD matrix has nonzero determinant. -/
theorem det_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) : A.det ≠ 0 :=
  hA.det_pos.ne'

/-- **Every diagonal entry of an SPD matrix is positive.** -/
theorem diag_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) (i : Fin n) :
    0 < A i i := by
  exact hA.posDef.diag_pos

/-- An SPD matrix is invertible. -/
theorem isUnit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) : IsUnit A := by
  exact hA.posDef.isUnit

/-- An SPD matrix is injective on vectors: `A·x = 0` implies `x = 0`. -/
theorem mulVec_injective {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymPosDef A) :
    Function.Injective A.mulVec := by
  exact A.mulVec_injective_iff_isUnit.2 hA.isUnit

end IsSymPosDef

/-- `AᵀA` is symmetric for every `A`. -/
lemma mul_transpose_isSymm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : (Aᵀ * A).IsSymm := by
  rw [← Matrix.isHermitian_iff_isSymm]
  simpa using (Matrix.isHermitian_conjTranspose_mul_self A)

/-- The adjoint identity over the reals: `(A·v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ·w)`. -/
lemma dot_mulVec_dotProduct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ)
    (w : Fin m → ℝ) : (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [← Matrix.vecMul_transpose]
  rw [Matrix.dotProduct_mulVec]

/-- If `A` has full column rank (`A.mulVec` injective), then `AᵀA` is symmetric
positive-definite.  This is the nonsingularity of the Gram matrix that makes the
normal equations uniquely solvable. -/
theorem posDef_mul_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.mulVec) : IsSymPosDef (Aᵀ * A) := by
  constructor
  · exact mul_transpose_isSymm A
  · intro x hx
    rw [← Matrix.mulVec_mulVec]
    rw [← dot_mulVec_dotProduct A x (A *ᵥ x)]
    have hAx : A *ᵥ x ≠ 0 := by
      intro h
      exact hx (hA (by simpa using h))
    simpa using (Matrix.dotProduct_self_star_pos_iff).2 hAx

end SymPosDef

section LeastSquares

/-- The squared Euclidean 2-norm of the residual `A·x - b`: the objective that
least-squares approximation minimizes. -/
def residualSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)

/-- If `xh` satisfies the normal equations, the residual `A·xh - b` is
orthogonal to the column space of `A`. -/
lemma residual_orthogonal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xh : Fin n → ℝ) (h : Aᵀ *ᵥ (A *ᵥ xh - b) = 0) (x : Fin n → ℝ) :
    (A *ᵥ (x - xh)) ⬝ᵥ (A *ᵥ xh - b) = 0 := by
  rw [dot_mulVec_dotProduct A (x - xh) (A *ᵥ xh - b)]
  rw [h]
  simp

/-- **Pythagorean decomposition.**  When `xh` satisfies the normal equations,
the squared residual at any `x` splits as the squared residual at `xh` plus the
squared norm of `A·(x - xh)`:
`‖A·x - b‖₂² = ‖A·xh - b‖₂² + ‖A·(x - xh)‖₂²`. -/
lemma residual_sq_decomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xh : Fin n → ℝ) (h : Aᵀ *ᵥ (A *ᵥ xh - b) = 0) (x : Fin n → ℝ) :
    residualSq A b x = residualSq A b xh + (A *ᵥ (x - xh)) ⬝ᵥ (A *ᵥ (x - xh)) := by
  have hdec : ∀ r d : Fin m → ℝ,
      (r + d) ⬝ᵥ (r + d) = r ⬝ᵥ r + 2 * (r ⬝ᵥ d) + d ⬝ᵥ d := by
    intro r d
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm d r]
    ring
  have hx : A *ᵥ x - b = (A *ᵥ xh - b) + A *ᵥ (x - xh) := by
    rw [Matrix.mulVec_sub]
    abel
  rw [residualSq, hx]
  rw [hdec (A *ᵥ xh - b) (A *ᵥ (x - xh))]
  have hcross : (A *ᵥ xh - b) ⬝ᵥ (A *ᵥ (x - xh)) = 0 := by
    rw [dotProduct_comm]
    exact residual_orthogonal A b xh h x
  rw [hcross]
  rw [residualSq]
  ring

/--
**Theorem 28.4 (least-squares approximation).**  If `xh` satisfies the normal
equations `Aᵀ·(A·xh - b) = 0`, then `xh` minimizes the squared residual
`‖A·x - b‖₂²` over all `x`.
-/
theorem normal_equations_minimizes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xh : Fin n → ℝ) (h : Aᵀ *ᵥ (A *ᵥ xh - b) = 0) (x : Fin n → ℝ) :
    residualSq A b xh ≤ residualSq A b x := by
  rw [residual_sq_decomposition A b xh h x]
  have hnonneg : 0 ≤ (A *ᵥ (x - xh)) ⬝ᵥ (A *ᵥ (x - xh)) := by
    simpa using (dotProduct_self_star_nonneg (A *ᵥ (x - xh)))
  linarith

/-- When `A` has full column rank, the minimizer of the squared residual is
unique. -/
theorem normal_equations_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xh : Fin n → ℝ) (hA : Function.Injective A.mulVec)
    (h : Aᵀ *ᵥ (A *ᵥ xh - b) = 0) (x : Fin n → ℝ) (heq : residualSq A b x = residualSq A b xh) :
    x = xh := by
  have hdec := residual_sq_decomposition A b xh h x
  have hd : (A *ᵥ (x - xh)) ⬝ᵥ (A *ᵥ (x - xh)) = 0 := by
    linarith
  have hAx : A *ᵥ (x - xh) = 0 := by
    exact (dotProduct_self_star_eq_zero.mp (by simpa using hd))
  have hsub : x - xh = 0 := hA (by simpa using hAx)
  ext i
  have hi : x i - xh i = 0 := congr_fun hsub i
  linarith

set_option linter.unnecessarySimpa false in
/-- **Closed-form least-squares solution.**  When `A` has full column rank,
`xh = (AᵀA)⁻¹·(Aᵀ·b)` satisfies the normal equations. -/
theorem least_squares_closed_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : Function.Injective A.mulVec) :
    Aᵀ *ᵥ (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) - b) = 0 := by
  have hPD : (Aᵀ * A).PosDef := by
    simpa using (Matrix.PosDef.conjTranspose_mul_self A hA)
  have hcancel : (Aᵀ * A) * (Aᵀ * A)⁻¹ = 1 := by
    letI := hPD.isUnit.invertible
    simpa using (Matrix.mul_inv_cancel_right_of_invertible (1 : Matrix (Fin n) (Fin n) ℝ))
  have hx : (Aᵀ * A) *ᵥ ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) = Aᵀ *ᵥ b := by
    rw [Matrix.mulVec_mulVec]
    rw [hcancel]
    simp
  calc
    Aᵀ *ᵥ (A *ᵥ ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) - b)
        = (Aᵀ * A) *ᵥ ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) - Aᵀ *ᵥ b := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    _ = Aᵀ *ᵥ b - Aᵀ *ᵥ b := by rw [hx]
    _ = 0 := by abel

/-- The closed-form least-squares solution `(AᵀA)⁻¹·Aᵀ·b` minimizes the squared
residual. -/
theorem least_squares_closed_form_minimizes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : Function.Injective A.mulVec) (x : Fin n → ℝ) :
    residualSq A b ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ≤ residualSq A b x := by
  exact normal_equations_minimizes A b ((Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b))
    (least_squares_closed_form A b hA) x

end LeastSquares

section Cholesky

/-- The **Schur complement** of the leading `1×1` block of `A`: with
`a = A 0 0` and the first-column vector `v i = A (Fin.succ i) 0`, it is
`S = A₂₂ - (v·vᵀ)/a`, the trailing block after one step of Gaussian elimination. -/
noncomputable def choleskySchur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A (Fin.succ i) (Fin.succ j) - (A (Fin.succ i) 0 * A 0 (Fin.succ j)) / A 0 0

/-- The dot product over `Fin 1` is a product. -/
@[simp]
lemma dotProduct_const_fin_one (t w : ℝ) :
    (fun _ : Fin 1 => t) ⬝ᵥ (fun _ : Fin 1 => w) = t * w := by
  unfold dotProduct
  rw [Fin.sum_univ_succ]
  simp

/-- Dot product distributes over a pointwise scalar multiple. -/
@[simp]
lemma dotProduct_add_scalar {n : ℕ} (y v : Fin n → ℝ) (t : ℝ) (w : Fin n → ℝ) :
    y ⬝ᵥ (fun i => v i * t + w i) = t * (v ⬝ᵥ y) + y ⬝ᵥ w := by
  unfold dotProduct
  rw [show (∑ i, y i * (v i * t + w i)) = ∑ i, (t * (y i * v i) + y i * w i) by
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  congr 1
  rw [show (∑ i, y i * v i) = ∑ i, v i * y i by
    apply Finset.sum_congr rfl
    intro i hi
    ring]

/-- Extracting a scalar factor from a dot product. -/
@[simp]
lemma dotProduct_smul_div {n : ℕ} (y v : Fin n → ℝ) (c : ℝ) :
    y ⬝ᵥ (fun i => v i * (v ⬝ᵥ y) / c) = (v ⬝ᵥ y) ^ 2 / c := by
  change (∑ i : Fin n, y i * (v i * (v ⬝ᵥ y) / c)) = (v ⬝ᵥ y) ^ 2 / c
  rw [show (∑ i, y i * (v i * (v ⬝ᵥ y) / c)) = (v ⬝ᵥ y) / c * (∑ i, v i * y i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [show (∑ i, v i * y i) = v ⬝ᵥ y by rfl]
  ring

/-- The quadratic form of the reindexed vector `z = u ∘ re` equals the quadratic
form of `u` under the reindexed matrix. -/
lemma reindex_quadratic {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (re : Fin (n + 1) ≃ Fin 1 ⊕ Fin n) (u : Fin 1 ⊕ Fin n → ℝ) :
    (u ∘ re) ⬝ᵥ (A *ᵥ (u ∘ re)) = u ⬝ᵥ ((A.reindex re re) *ᵥ u) := by
  have hmul : A *ᵥ (u ∘ re) = (A.reindex re re *ᵥ u) ∘ re := by
    funext i
    change (∑ j : Fin (n + 1), A i j * (u ∘ re) j) =
      ∑ s : Fin 1 ⊕ Fin n, (A.reindex re re) (re i) s * u s
    rw [← Equiv.sum_comp re.symm]
    apply Finset.sum_congr rfl
    intro s hs
    simp [Matrix.reindex_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rw [hmul]
  unfold dotProduct
  rw [← Equiv.sum_comp re.symm]
  apply Finset.sum_congr rfl
  intro s hs
  simp [Equiv.apply_symm_apply]

/-- Reindexing `A` by `finOneSumFin` views it as the block matrix with entries
`[[A 0 0, A 0 (succ j)], [A (succ i) 0, A (succ i) (succ j)]]`. -/
lemma reindex_fromBlocks {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.reindex (finOneSumFin n) (finOneSumFin n) = Matrix.fromBlocks
      (fun _ _ : Fin 1 => A 0 0)
      (fun (_ : Fin 1) j => A 0 (Fin.succ j))
      (fun i (_ : Fin 1) => A (Fin.succ i) 0)
      (fun i j : Fin n => A (Fin.succ i) (Fin.succ j)) := by
  rw [Matrix.ext_iff_blocks]
  constructor
  · ext i j
    simp [Matrix.reindex_apply, finOneSumFin, Matrix.toBlocks₁₁]
  · constructor
    · ext i j
      simp [Matrix.reindex_apply, finOneSumFin, Matrix.toBlocks₁₂]
    · constructor
      · ext i j
        simp [Matrix.reindex_apply, finOneSumFin, Matrix.toBlocks₂₁]
      · ext i j
        simp [Matrix.reindex_apply, finOneSumFin, Matrix.toBlocks₂₂]

/-- **Block quadratic form.**  For `z = (t, y)` (the vector `0 ↦ t`,
`succ i ↦ y i`), `zᵀAz` expands as
`a·t² + 2·t·(v ⬝ᵥ y) + yᵀA₂₂y` where `a = A 0 0`, `v i = A (Fin.succ i) 0`,
and `A₂₂` is the trailing block.  This is the algebraic core of the Cholesky
recursion. -/
lemma schur_quadratic_form {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.IsSymm) (t : ℝ) (y : Fin n → ℝ) :
    let a : ℝ := A 0 0
    let v : Fin n → ℝ := fun i => A (Fin.succ i) 0
    let A22 : Matrix (Fin n) (Fin n) ℝ := fun i j => A (Fin.succ i) (Fin.succ j)
    let z : Fin (n + 1) → ℝ := (Sum.elim (fun _ : Fin 1 => t) y) ∘ (finOneSumFin n)
    z ⬝ᵥ (A *ᵥ z) = a * t ^ 2 + 2 * t * (v ⬝ᵥ y) + y ⬝ᵥ (A22 *ᵥ y) := by
  intro a v A22 z
  dsimp [z]
  rw [reindex_quadratic A (finOneSumFin n) (Sum.elim (fun _ : Fin 1 => t) y)]
  rw [reindex_fromBlocks A]
  let A11 : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => A 0 0
  let A12 : Matrix (Fin 1) (Fin n) ℝ := fun _ j => A 0 (Fin.succ j)
  let A21 : Matrix (Fin n) (Fin 1) ℝ := fun i _ => A (Fin.succ i) 0
  let A22b : Matrix (Fin n) (Fin n) ℝ := fun i j => A (Fin.succ i) (Fin.succ j)
  rw [Matrix.fromBlocks_mulVec]
  rw [sumElim_dotProduct_sumElim]
  have hu_inl : (Sum.elim (fun _ : Fin 1 => t) y) ∘ Sum.inl = (fun _ : Fin 1 => t) := by
    funext x
    simp
  have hu_inr : (Sum.elim (fun _ : Fin 1 => t) y) ∘ Sum.inr = y := by
    funext x
    simp
  rw [hu_inl, hu_inr]
  have h11 : A11 *ᵥ (fun _ : Fin 1 => t) = fun _ : Fin 1 => a * t := by
    ext i
    simp [A11, Matrix.mulVec, a]
  have h12 : A12 *ᵥ y = fun _ : Fin 1 => v ⬝ᵥ y := by
    ext i
    simp [A12, Matrix.mulVec, v]
    congr 1
    funext j
    exact (Matrix.IsSymm.ext_iff.mp hA) (Fin.succ j) 0
  have h21 : A21 *ᵥ (fun _ : Fin 1 => t) = fun i : Fin n => v i * t := by
    ext i
    simp [A21, Matrix.mulVec, v]
  have h22 : A22b *ᵥ y = A22 *ᵥ y := by
    rfl
  rw [h11, h12, h21, h22]
  change (fun _ : Fin 1 => t) ⬝ᵥ (fun _ : Fin 1 => a * t + (v ⬝ᵥ y)) +
    y ⬝ᵥ (fun i : Fin n => v i * t + (A22 *ᵥ y) i) =
    a * t ^ 2 + 2 * t * (v ⬝ᵥ y) + y ⬝ᵥ (A22 *ᵥ y)
  rw [dotProduct_const_fin_one t (a * t + (v ⬝ᵥ y))]
  rw [dotProduct_add_scalar y v t (A22 *ᵥ y)]
  ring

/-- Entrywise expansion of the Schur complement acting on `y`:
`(S·y) i = (A₂₂·y) i - v i·(v ⬝ᵥ y)/a`. -/
lemma schur_mulVec {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsSymm)
    (y : Fin n → ℝ) :
    (choleskySchur A *ᵥ y) = fun i =>
      ((fun j : Fin n => A (Fin.succ i) (Fin.succ j)) ⬝ᵥ y) -
        (A (Fin.succ i) 0 * ((fun j : Fin n => A (Fin.succ j) 0) ⬝ᵥ y)) / A 0 0 := by
  funext i
  unfold choleskySchur Matrix.mulVec dotProduct
  rw [show (∑ j, (A (Fin.succ i) (Fin.succ j) - (A (Fin.succ i) 0 * A 0 (Fin.succ j)) / A 0 0) * y j) =
      (∑ j, A (Fin.succ i) (Fin.succ j) * y j) -
        A (Fin.succ i) 0 * (∑ j, A (Fin.succ j) 0 * y j) / A 0 0 by
    rw [show (∑ j, (A (Fin.succ i) (Fin.succ j) - (A (Fin.succ i) 0 * A 0 (Fin.succ j)) / A 0 0) * y j) =
        ∑ j, (A (Fin.succ i) (Fin.succ j) * y j -
          (A (Fin.succ i) 0 * A 0 (Fin.succ j)) / A 0 0 * y j) by
      apply Finset.sum_congr rfl
      intro j hj
      ring]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [show (∑ j, (A (Fin.succ i) 0 * A 0 (Fin.succ j)) / A 0 0 * y j) =
          A (Fin.succ i) 0 * (∑ j, A (Fin.succ j) 0 * y j) / A 0 0 by
        rw [show (∑ j, (A (Fin.succ i) 0 * A 0 (Fin.succ j)) / A 0 0 * y j) =
            (A (Fin.succ i) 0 / A 0 0) * (∑ j, A 0 (Fin.succ j) * y j) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring]
        rw [show (∑ j, A 0 (Fin.succ j) * y j) = ∑ j, A (Fin.succ j) 0 * y j by
          apply Finset.sum_congr rfl
          intro j hj
          exact congrArg (fun x => x * y j) (Matrix.IsSymm.ext_iff.mp hA (Fin.succ j) 0)]
        ring]]

/-- The quadratic form of the Schur complement: `yᵀSy = yᵀA₂₂y - (v ⬝ᵥ y)²/a`. -/
lemma schur_residual {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsSymm)
    (y : Fin n → ℝ) :
    y ⬝ᵥ (choleskySchur A *ᵥ y) =
      y ⬝ᵥ ((fun i j : Fin n => A (Fin.succ i) (Fin.succ j)) *ᵥ y) -
        ((fun i : Fin n => A (Fin.succ i) 0) ⬝ᵥ y) ^ 2 / A 0 0 := by
  rw [schur_mulVec A hA y]
  let W : Fin n → ℝ := fun i => (fun j : Fin n => A (Fin.succ i) (Fin.succ j)) ⬝ᵥ y
  let Z : Fin n → ℝ := fun i =>
    A (Fin.succ i) 0 * ((fun j : Fin n => A (Fin.succ j) 0) ⬝ᵥ y) / A 0 0
  change y ⬝ᵥ (W - Z) =
    y ⬝ᵥ ((fun i j : Fin n => A (Fin.succ i) (Fin.succ j)) *ᵥ y) -
      ((fun i : Fin n => A (Fin.succ i) 0) ⬝ᵥ y) ^ 2 / A 0 0
  rw [dotProduct_sub]
  congr 1
  rw [dotProduct_smul_div y (fun i => A (Fin.succ i) 0) (A 0 0)]

/-- **The Schur complement of an SPD matrix is SPD.**  This is the strict
version of the PSD `Matrix.PosSemidef.fromBlocks₁₁` fact, proved directly: for
`y ≠ 0`, the vector `z = (t, y)` with `t = -(v ⬝ᵥ y)/a` satisfies `zᵀAz = yᵀSy`,
so positivity of `A` transfers to `S`.  This is the induction step of the
Cholesky recursion (CLRS §28.3). -/
theorem cholesky_schur_complement {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : IsSymPosDef A) : IsSymPosDef (choleskySchur A) := by
  constructor
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    unfold choleskySchur
    have hs := Matrix.IsSymm.ext_iff.mp hA.isSymm
    rw [hs (Fin.succ j) (Fin.succ i), hs 0 (Fin.succ i), hs (Fin.succ j) 0]
    ring
  · intro y hy
    let a : ℝ := A 0 0
    let v : Fin n → ℝ := fun i => A (Fin.succ i) 0
    let A22 : Matrix (Fin n) (Fin n) ℝ := fun i j => A (Fin.succ i) (Fin.succ j)
    let S := choleskySchur A
    have ha : a ≠ 0 := ne_of_gt (hA.diag_pos 0)
    let t : ℝ := -(v ⬝ᵥ y) / a
    let z : Fin (n + 1) → ℝ := (Sum.elim (fun _ : Fin 1 => t) y) ∘ (finOneSumFin n)
    have hz : z ≠ 0 := by
      intro hz0
      apply hy
      funext i
      have hzi : z (Fin.succ i) = 0 := congr_fun hz0 (Fin.succ i)
      simpa [z, finOneSumFin] using hzi
    have ht2 : a * t ^ 2 + 2 * t * (v ⬝ᵥ y) = -(v ⬝ᵥ y) ^ 2 / a := by
      dsimp [t]
      field_simp [ha]
      ring
    have hres : y ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (A22 *ᵥ y) - (v ⬝ᵥ y) ^ 2 / a := by
      dsimp [S, A22, v, a]
      rw [schur_residual A hA.isSymm y]
    have hquad : z ⬝ᵥ (A *ᵥ z) = a * t ^ 2 + 2 * t * (v ⬝ᵥ y) + y ⬝ᵥ (A22 *ᵥ y) := by
      dsimp [a, v, A22, t, z]
      exact schur_quadratic_form hA.isSymm t y
    have hexp : z ⬝ᵥ (A *ᵥ z) = y ⬝ᵥ (S *ᵥ y) := by
      rw [hquad, ht2]
      rw [hres]
      ring
    have hpos : 0 < z ⬝ᵥ (A *ᵥ z) := hA.dotProduct_pos hz
    rw [hexp] at hpos
    exact hpos

/-- The **Cholesky factor** for the recursion step: with `a = A 0 0` and the
first-column vector `v i = A (Fin.succ i) 0`, `choleskyFactor A L2` is the block
lower-triangular matrix `[[√a, 0], [v/√a, L2]]` over `Fin (n+1)` built from the
scalar `√a`, the column `v/√a`, and the trailing factor `L2`. -/
noncomputable def choleskyFactor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    Fin.cases
      (fun j : Fin (n + 1) => if j = 0 then Real.sqrt (A 0 0) else 0)
      (fun i' : Fin n => fun j : Fin (n + 1) =>
        Fin.cases (A (Fin.succ i') 0 / Real.sqrt (A 0 0)) (fun j' : Fin n => L2 i' j') j)
      i j

/-- The top-left entry of the Cholesky factor is `√a`. -/
@[simp]
lemma choleskyFactor_00 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) : choleskyFactor A L2 0 0 = Real.sqrt (A 0 0) := by
  simp [choleskyFactor]

/-- The first row of the Cholesky factor (right of the diagonal) is zero. -/
@[simp]
lemma choleskyFactor_0_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : choleskyFactor A L2 0 (Fin.succ j) = 0 := by
  simp [choleskyFactor]

/-- The first column of the Cholesky factor (below the diagonal) is `v/√a`. -/
@[simp]
lemma choleskyFactor_succ_0 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    choleskyFactor A L2 (Fin.succ i) 0 = A (Fin.succ i) 0 / Real.sqrt (A 0 0) := by
  simp [choleskyFactor]

/-- The trailing block of the Cholesky factor is `L2`. -/
@[simp]
lemma choleskyFactor_succ_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    choleskyFactor A L2 (Fin.succ i) (Fin.succ j) = L2 i j := by
  simp [choleskyFactor]

/-- `L` is **lower-triangular with positive diagonal**: every entry above the
main diagonal is zero and every diagonal entry is strictly positive. -/
def IsLowerTriangularPosDiag {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ ⦃i j : Fin n⦄, i < j → L i j = 0) ∧ (∀ i : Fin n, 0 < L i i)

/-- The `(0,0)` entry of `L·Lᵀ` for the Cholesky factor is `a = A 0 0`. -/
lemma choleskyFactor_mul_00 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (hpos : 0 < A 0 0) :
    (choleskyFactor A L2 * (choleskyFactor A L2)ᵀ) 0 0 = A 0 0 := by
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  simp
  simpa [pow_two] using (Real.sq_sqrt hpos.le)

/-- The `(0, j)` entries of `L·Lᵀ` for the Cholesky factor match `A`. -/
lemma choleskyFactor_mul_0_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hpos : 0 < A 0 0) (j : Fin n) :
    (choleskyFactor A L2 * (choleskyFactor A L2)ᵀ) 0 (Fin.succ j) = A 0 (Fin.succ j) := by
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  simp
  have hs_ne : Real.sqrt (A 0 0) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hv : A 0 (Fin.succ j) = A (Fin.succ j) 0 := by
    exact (Matrix.IsSymm.ext_iff.mp hA) (Fin.succ j) 0
  rw [hv]
  field_simp [hs_ne]

/-- The `(i, 0)` entries of `L·Lᵀ` for the Cholesky factor match `A`. -/
lemma choleskyFactor_mul_succ_0 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (hpos : 0 < A 0 0) (i : Fin n) :
    (choleskyFactor A L2 * (choleskyFactor A L2)ᵀ) (Fin.succ i) 0 = A (Fin.succ i) 0 := by
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  simp
  have hs_ne : Real.sqrt (A 0 0) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  field_simp [hs_ne]

/-- Entrywise expansion of the trailing block of `L·Lᵀ`:
`(L·Lᵀ)ᵢⱼ = (vᵢ/√a)·(vⱼ/√a) + (L2·L2ᵀ)ᵢⱼ`. -/
lemma choleskyFactor_mul_succ_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (choleskyFactor A L2 * (choleskyFactor A L2)ᵀ) (Fin.succ i) (Fin.succ j) =
      (A (Fin.succ i) 0 / Real.sqrt (A 0 0)) * (A (Fin.succ j) 0 / Real.sqrt (A 0 0)) +
        (L2 * L2ᵀ) i j := by
  rw [Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  simp [Matrix.mul_apply, Matrix.transpose_apply]

/-- When `L2·L2ᵀ` is the Schur complement, the trailing block of `L·Lᵀ` matches
the trailing block of `A`. -/
lemma choleskyFactor_mul_succ_succ_eq {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (L2 : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hpos : 0 < A 0 0) (i j : Fin n)
    (hL2 : choleskySchur A = L2 * L2ᵀ) :
    (choleskyFactor A L2 * (choleskyFactor A L2)ᵀ) (Fin.succ i) (Fin.succ j) = A (Fin.succ i) (Fin.succ j) := by
  rw [choleskyFactor_mul_succ_succ A L2 i j]
  rw [← hL2]
  unfold choleskySchur
  have hsym : A 0 (Fin.succ j) = A (Fin.succ j) 0 := by
    exact (Matrix.IsSymm.ext_iff.mp hA) (Fin.succ j) 0
  rw [hsym]
  have hs_ne : Real.sqrt (A 0 0) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have hs_sq : (Real.sqrt (A 0 0)) ^ 2 = A 0 0 := Real.sq_sqrt hpos.le
  field_simp [hs_ne, hpos.ne']
  ring_nf
  rw [hs_sq]
  ring

/--
**Cholesky decomposition (CLRS Theorem 28.3).**  Every symmetric
positive-definite matrix `A` factors as `A = L·Lᵀ` with `L` lower-triangular
with positive diagonal.

The proof is the block recursion: writing `a = A 0 0`, `v i = A (Fin.succ i) 0`,
and `S` for the Schur complement `A₂₂ - v·vᵀ/a`, the strict positivity of `A`
makes `S` SPD (`cholesky_schur_complement`), so by induction
`S = L₂·L₂ᵀ`.  The factor `L = [[√a, 0],[v/√a, L₂]]`
(`choleskyFactor`) is lower-triangular with positive diagonal and satisfies
`L·Lᵀ = A`.
-/
theorem cholesky_decomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSymPosDef A) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ, IsLowerTriangularPosDiag L ∧ A = L * Lᵀ := by
  induction n with
  | zero =>
      refine ⟨1, ?tri, ?eq⟩
      · constructor
        · intro i j hij
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      · ext i j
        exact Fin.elim0 i
  | succ n ih =>
      let a : ℝ := A 0 0
      let S : Matrix (Fin n) (Fin n) ℝ := choleskySchur A
      have ha : 0 < a := by simpa [a] using hA.diag_pos 0
      have hS : IsSymPosDef S := by simpa [S] using cholesky_schur_complement hA
      rcases ih S hS with ⟨L2, ⟨hL2lt, hL2pd⟩, hL2eq⟩
      let L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := choleskyFactor A L2
      refine ⟨L, ?tri', ?eq'⟩
      · constructor
        · intro i j hij
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · simp at hij
            · simp [L]
          · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
            · simp at hij
            · have hij' : i' < j' := by simpa using hij
              simpa [L] using (hL2lt hij')
        · intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · simpa [L, a] using (Real.sqrt_pos.2 ha)
          · simpa [L] using (hL2pd i')
      · ext i j
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · simpa [L, a] using (choleskyFactor_mul_00 A L2 ha).symm
          · simpa [L] using (choleskyFactor_mul_0_succ A L2 hA.isSymm ha j').symm
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · simpa [L] using (choleskyFactor_mul_succ_0 A L2 ha i').symm
          · simpa [L] using (choleskyFactor_mul_succ_succ_eq A L2 hA.isSymm ha i' j' hL2eq).symm

end Cholesky

end Chapter28

end CLRS
