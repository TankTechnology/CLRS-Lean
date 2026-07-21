import CLRSLean.Chapter_28.Section_28_1_LUP_Decomposition
import Mathlib

/-!
# Sections 28.2–28.3 — Matrix Inversion, SPD Matrices, and Least-Squares

This file formalizes:

- **Section 28.2 (Matrix inversion):** Given a nonsingular `n × n` matrix
  `A`, compute `A⁻¹` by solving `AXⱼ = eⱼ` for each standard basis vector
  `eⱼ` (column `j` of the identity) using LUP-SOLVE.  Prove
  `A * A⁻¹ = I` (and state `A⁻¹ * A = I`).

- **Section 28.3 (Symmetric positive-definite matrices and least-squares
  approximation):**
  * `SPDMatrix` predicate: an `n × n` real matrix `A` is **symmetric
    positive-definite** if `A.transpose = A` and `xᵀ A x > 0` for every nonzero
    vector `x`.
  * LDLᵀ decomposition for SPD matrices: `A = L D L.transpose` where `L` is unit
    lower triangular and `D` is diagonal with positive entries.
  * Least-squares approximation: given an `m × n` matrix `A` (with `m ≥ n`
    and full column rank) and observation vector `b`, solve the normal
    equations `A.transpose * A * x = A.transpose * b`.

All nontrivial proofs are deferred (`sorry`); the focus is on laying down
the formal definitions, theorem interfaces, and connecting §28.2–28.3 to
the LUP decomposition from §28.1.

**Notation conventions used in this section:**

- `A`, `L`, `U`, `D`, `Ainv` : `Mat n n` (square matrices)
- `b`, `x`, `y`, `eᵢ` : `Vec n` (vectors)
- `Arect` : `Mat m n` (rectangular for least-squares)
-/

namespace CLRS
namespace Chapter28

/-! ## Standard basis vectors -/

/--
The `i`-th **standard basis vector** of length `n`:
`eⱼ[k] = 1` when `k = j` and `eⱼ[k] = 0` otherwise.
-/
def stdBasis (n : ℕ) (j : Fin n) : Vec n :=
  λ k => if k = j then 1 else 0

/-! ### Section 28.2 — Matrix inversion via LUP decomposition -/

/--
**Matrix inverse** computed column-by-column using LUP-SOLVE (CLRS §28.2).

For a nonsingular `n × n` matrix `A`, the inverse `A⁻¹` consists of
columns `X₀, …, X_{n-1}` where each `Xⱼ` solves `A Xⱼ = eⱼ` (the
standard basis vector).  LUP-SOLVE is used for each column.

Noncomputable (inherits noncomputability of `lupSolve`).
-/
noncomputable def matrixInverse (A : Mat n n) : Mat n n :=
  λ i j => lupSolve A (stdBasis n j) i

/--
**Inverse right-multiplication property** (CLRS Theorem 28.3).

For a nonsingular matrix `A`, `A * A⁻¹ = I`.  Proved column-wise:
column `j` of `A * A⁻¹` is `A * Xⱼ = eⱼ` by `lupSolve_correct`.
-/
theorem matrixInverse_mul_eq_one (A : Mat n n) :
    A * matrixInverse A = 1 := by
  ext i j
  -- Need to show: (A * A⁻¹) i j = I i j
  -- (A * A⁻¹) i j = ∑ k, A i k * (matrixInverse A) k j
  -- = ∑ k, A i k * lupSolve A (stdBasis n j) k
  -- = (Matrix.mulVec A (lupSolve A (stdBasis n j))) i
  -- = (stdBasis n j) i   [by lupSolve_correct]
  -- = (if i = j then 1 else 0)
  -- = 1 i j
  have h := lupSolve_correct A (stdBasis n j)
  -- h : Matrix.mulVec A (lupSolve A (stdBasis n j)) = stdBasis n j
  have hi := congrFun h i
  -- hi : (Matrix.mulVec A (lupSolve A (stdBasis n j))) i = (stdBasis n j) i
  simp [matrixInverse, Matrix.mul_apply, Matrix.one_apply, Matrix.mulVec, stdBasis] at hi ⊢
  -- hi: (∑ k : Fin n, A i k * lupSolve A (stdBasis n j) k) = (if i = j then 1 else 0)
  -- Goal: ∑ k : Fin n, A i k * lupSolve A (stdBasis n j) k = if i = j then 1 else 0
  exact hi

/--
**Inverse left-multiplication property** (CLRS Theorem 28.3, second part).

For a nonsingular matrix `A`, `A⁻¹ * A = I`.  This follows from
`A * A⁻¹ = I` plus the fact that a one-sided inverse of a square matrix
is also a two-sided inverse (requires the matrix to be a unit in the
matrix ring, i.e., nonsingular).
-/
theorem one_mul_matrixInverse_eq_one (A : Mat n n) :
    matrixInverse A * A = 1 := by
  have h := matrixInverse_mul_eq_one A
  -- h: A * matrixInverse A = 1
  -- In the ring of square matrices, a * b = 1 ↔ b * a = 1
  exact (Matrix.mul_eq_one_comm.mp h)

/-! #### Column-wise inverse computation -/

/--
**Inverse column correctness:** column `j` of `A⁻¹` solves `A Xⱼ = eⱼ`.

This is the defining property for the column-by-column computation.
-/
theorem matrixInverse_column_spec (A : Mat n n) (j : Fin n) :
    Matrix.mulVec A (λ i => matrixInverse A i j) = stdBasis n j := by
  ext k
  simp [matrixInverse, stdBasis, Matrix.mulVec]
  exact congrFun (lupSolve_correct A (stdBasis n j)) k

/-! ### Section 28.3 — Symmetric positive-definite matrices -/

/--
A square matrix `A` is **symmetric** if `A.transpose = A`.
-/
def IsSymmetric (A : Mat n n) : Prop :=
  A.transpose = A

/--
A symmetric matrix `A` is **positive-definite** if for every nonzero
vector `x`, the quadratic form `xᵀ A x` is positive.

Formally: `∀ x : Vec n, x ≠ (λ _ => 0) → (∑ i, x i * (A * x) i) > 0`.
-/
def IsPositiveDefinite (A : Mat n n) : Prop :=
  ∀ (x : Vec n), x ≠ (λ _ => (0 : ℝ)) → (∑ i : Fin n, x i * (Matrix.mulVec A x) i) > (0 : ℝ)

/--
A **symmetric positive-definite (SPD) matrix** is one that is both
symmetric and positive-definite (CLRS §28.3).
-/
def SPDMatrix (A : Mat n n) : Prop :=
  IsSymmetric A ∧ IsPositiveDefinite A

/-- The all-ones vector of length `n`. Useful for constructing examples. -/
def onesVec (n : ℕ) : Vec n := λ _ => 1

/-- The all-zeros vector of length `n`. -/
def zerosVec (n : ℕ) : Vec n := λ _ => 0

/-! #### Properties of SPD matrices -/

/--
**Positive-definite implies all diagonal entries are positive.**

If `A` is positive-definite, then `A i i > 0` for every `i` (use
`x = eⱼ` in the definition).
-/
theorem positiveDefinite_diag_pos {A : Mat n n} (h : IsPositiveDefinite A)
    (i : Fin n) : A i i > 0 := by
  -- Take x = eᵢ (standard basis vector).  Then xᵀ A x = A i i > 0.
  let e := stdBasis n i
  have he_nonzero : e ≠ (λ _ => (0 : ℝ)) := by
    intro hzero
    have h := congrFun hzero i
    simp [e, stdBasis] at h
  have hpos := h e he_nonzero
  -- hpos : (∑ k : Fin n, e k * (Matrix.mulVec A e) k) > 0
  -- Compute the sum: only the i-th term is nonzero
  have hsum : (∑ k : Fin n, e k * (Matrix.mulVec A e) k) = A i i := by
    calc
      (∑ k : Fin n, e k * (Matrix.mulVec A e) k)
          = (∑ k : Fin n, e k * (∑ j : Fin n, A k j * e j)) := rfl
      _ = (∑ k : Fin n, e k * A k i) := by
        refine Finset.sum_congr rfl (λ k hk => ?_)
        simp [e, stdBasis, Matrix.mulVec]
      _ = A i i := by
        simp [e, stdBasis]
  linarith

/--
**SPD matrices have positive diagonal entries.**
-/
theorem SPDMatrix_diag_pos {A : Mat n n} (h : SPDMatrix A) (i : Fin n) :
    A i i > 0 :=
  positiveDefinite_diag_pos h.2 i

/-! ### LDLᵀ decomposition for SPD matrices -/

/--
An **LDLᵀ decomposition** of a symmetric positive-definite matrix `A`
(CLRS §28.3).

Consists of:

- `L` : unit lower triangular `n × n` matrix
- `D` : diagonal `n × n` matrix with positive entries

Satisfying `A = L * D * L.transpose`.
-/
structure LDLTDecomp (A : Mat n n) where
  /-- Unit lower triangular matrix (1s on diagonal). -/
  L : Mat n n
  /-- Diagonal matrix with positive entries. -/
  D : Mat n n
  /-- `L` is unit lower triangular. -/
  hL : IsUnitLowerTriangular L
  /-- `D` is diagonal: `D i j = 0` for `i ≠ j`. -/
  hD_diag : ∀ i j : Fin n, i ≠ j → D i j = 0
  /-- Diagonal entries of `D` are positive. -/
  hD_pos : ∀ i : Fin n, D i i > 0
  /-- `A = L * D * L.transpose`. -/
  h_decomp : A = L * D * L.transpose

/--
Existence of an LDLᵀ decomposition for every SPD matrix.

(CLRS Theorem 28.4, the LDLᵀ decomposition theorem.)
-/
theorem ldltDecomp_exists {A : Mat n n} (h : SPDMatrix A) :
    Nonempty (LDLTDecomp A) := by
  sorry
  -- The CLRS proof constructs L and D iteratively:
  -- For j = 0, …, n-1:
  --   1. D[j,j] = A[j,j] - Σ_{k < j} L[j,k]² * D[k,k]
  --      (Cholesky-style without square roots)
  --   2. For i = j+1, …, n-1:
  --      L[i,j] = (A[i,j] - Σ_{k < j} L[i,k] * D[k,k] * L[j,k]) / D[j,j]
  -- The diagonal of L is 1 by construction.
  -- The SPD property guarantees D[j,j] > 0 at every step.

/--
**LDLᵀ decomposition** for an SPD matrix.

Noncomputable (uses `Classical.choice`).
-/
noncomputable def ldltDecomp (A : Mat n n) (h : SPDMatrix A) : LDLTDecomp A :=
  Classical.choice (ldltDecomp_exists h)

/--
The LDLᵀ decomposition satisfies `A = L * D * L.transpose`.
-/
theorem ldltDecomp_spec {A : Mat n n} (h : SPDMatrix A) :
    A = (ldltDecomp A h).L * (ldltDecomp A h).D * (ldltDecomp A h).L.transpose :=
  (ldltDecomp A h).h_decomp

/-! ### Least-squares approximation via normal equations -/

/--
**Least-squares solution** via the normal equations (CLRS §28.3).

Given an `m × n` matrix `A` (typically `m ≥ n`, full column rank) and
an observation vector `b` (length `m`), solve the normal equations
`A.transpose * A * x = A.transpose * b`
for the `n`-vector `x`.  The vector `x` minimizes `‖A x - b‖₂` over all
`x ∈ ℝⁿ`.

This definition uses LUP-SOLVE on the `n × n` matrix `A.transpose * A`.  The
noncomputability is inherited from `lupSolve`.
-/
noncomputable def leastSquares (A : Mat m n) (b : Vec m) : Vec n :=
  -- Form the normal matrix N = A.transpose * A  (size n × n)
  let N : Mat n n := A.transpose * A
  -- Form the right-hand side c = A.transpose * b (size n)
  let c : Vec n := Matrix.mulVec A.transpose b
  lupSolve N c

/--
**Normal equations correctness** (CLRS §28.3).

The least-squares solution `x` satisfies `A.transpose * A * x = A.transpose * b`.
-/
theorem leastSquares_normal_eq (A : Mat m n) (b : Vec m) :
    Matrix.mulVec (A.transpose * A) (leastSquares A b) = Matrix.mulVec A.transpose b := by
  unfold leastSquares
  exact lupSolve_correct (A.transpose * A) (Matrix.mulVec A.transpose b)

/--
**Least-squares residual orthogonality** (CLRS Theorem 28.5).

The residual `r = A x - b` is orthogonal to the column space of `A`,
i.e., `A.transpose * (A x - b) = 0`.  This follows directly from the normal
equations.
-/
theorem leastSquares_residual_orthogonal (A : Mat m n) (b : Vec m) :
    Matrix.mulVec A.transpose (Matrix.mulVec A (leastSquares A b) - b) = 0 := by
  -- From Aᵀ A x = Aᵀ b, we have Aᵀ (A x - b) = 0
  calc
    Matrix.mulVec A.transpose (Matrix.mulVec A (leastSquares A b) - b)
        = Matrix.mulVec A.transpose (Matrix.mulVec A (leastSquares A b))
          - Matrix.mulVec A.transpose b := by
      simp [Matrix.mulVec_sub]
    _ = Matrix.mulVec (A.transpose * A) (leastSquares A b) - Matrix.mulVec A.transpose b := by
      simp [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec A.transpose b - Matrix.mulVec A.transpose b := by
      rw [leastSquares_normal_eq]
    _ = 0 := by simp

/--
**Least-squares optimality** (CLRS Theorem 28.5, minimisation part).

The solution `x = leastSquares A b` minimises the squared Euclidean norm
`‖A x - b‖²` over all `x ∈ ℝⁿ`.  This follows from the orthogonality
principle: for any `y`, `‖A y - b‖² = ‖A x - b‖² + ‖A (y - x)‖²`.
-/
theorem leastSquares_optimal (A : Mat m n) (b : Vec m) (y : Vec n) :
    -- ‖A (leastSquares A b) - b‖² ≤ ‖A y - b‖²
    (∑ i : Fin m,
      (Matrix.mulVec A (leastSquares A b) i - b i) *
      (Matrix.mulVec A (leastSquares A b) i - b i)) ≤
    (∑ i : Fin m,
      (Matrix.mulVec A y i - b i) *
      (Matrix.mulVec A y i - b i)) := by
  sorry
  -- Proof uses the orthogonality principle:
  -- Let x = leastSquares A b, r = A x - b.
  -- For any y, let d = A (y - x).
  -- Then A y - b = r + d.
  -- ‖A y - b‖² = ‖r‖² + ‖d‖² + 2⟨r, d⟩.
  -- But ⟨r, d⟩ = rᵀ (A (y - x)) = (Aᵀ r)ᵀ (y - x) = 0 (by orthogonality).
  -- Hence ‖A y - b‖² = ‖r‖² + ‖d‖² ≥ ‖r‖² = ‖A x - b‖².

/-! #### Cholesky decomposition (bonus, closely related to LDLᵀ) -/

/--
A **Cholesky decomposition** of an SPD matrix `A` (CLRS-related).

`A = L * L.transpose` where `L` is lower triangular (not necessarily unit).

This is a special case of LDLᵀ where `D = I`.
-/
structure CholeskyDecomp (A : Mat n n) where
  /-- Lower triangular matrix. -/
  L : Mat n n
  /-- `L` is lower triangular. -/
  hL : IsLowerTriangular L
  /-- `A = L * L.transpose`. -/
  h_decomp : A = L * L.transpose

end Chapter28
end CLRS
