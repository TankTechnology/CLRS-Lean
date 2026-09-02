import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations

/-!
# 28.2 Inverting matrices

This section formalizes the matrix-inversion consequence of the LUP
decomposition (CLRS Theorem 28.2).  Once {lit}`A` has an LUP factorization
{lit}`σ.permMatrix · A = L · U` (Theorem 28.1), its inverse is obtained by
inverting the triangular factors and undoing the row permutation:
{lit}`A⁻¹ = U⁻¹ · L⁻¹ · σ.permMatrix`.

Main results:

- Theorem {lit}`inv_eq_lup`: from {lit}`σ.permMatrix · A = L · U` (with
  {lit}`σ.permMatrix` the permutation matrix), {lit}`A⁻¹ = U⁻¹ · L⁻¹ ·
  σ.permMatrix`.
- Lemma {lit}`permMatrix_inv`: the inverse of a permutation matrix is the
  permutation matrix of the inverse permutation.
- Lemma {lit}`permMatrix_mul_inv`: a permutation matrix left-multiplied by its
  inverse is the identity.

Notation conventions:

- {lit}`A` : an {lit}`n × n` matrix over a field {lit}`F`.
- {lit}`σ.permMatrix F` : the permutation matrix of {lit}`σ`.
- {lit}`M⁻¹` : the matrix inverse of {lit}`M` (zero for singular matrices).
-/

namespace CLRS

namespace Chapter28

open Matrix

variable {F : Type} [Field F]

/-- The inverse of a permutation matrix is the permutation matrix of the
inverse permutation: `(σ.permMatrix)⁻¹ = σ⁻¹.permMatrix`. -/
lemma permMatrix_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix F)⁻¹ = σ⁻¹.permMatrix F := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.permMatrix_mul]
  simp

/-- A permutation matrix left-multiplied by its inverse is the identity. -/
lemma permMatrix_mul_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix F)⁻¹ * σ.permMatrix F = 1 := by
  rw [permMatrix_inv]
  rw [← Matrix.permMatrix_mul]
  simp

/--
**Theorem 28.2 (inversion from the LUP decomposition).**  If
{lit}`σ.permMatrix · A = L · U` is an LUP factorization, then
{lit}`A⁻¹ = U⁻¹ · L⁻¹ · σ.permMatrix`: the inverse is obtained by inverting the
upper factor, then the lower factor, then undoing the row permutation.

Proof: apply the inverse to both sides of the factorization and use
{lit}`Matrix.mul_inv_rev` and the fact that a permutation matrix is invertible
with inverse {lit}`σ⁻¹.permMatrix`.
-/
theorem inv_eq_lup {n : ℕ} {A L U : Matrix (Fin n) (Fin n) F} {σ : Equiv.Perm (Fin n)}
    (hLUP : σ.permMatrix F * A = L * U) :
    A⁻¹ = U⁻¹ * L⁻¹ * σ.permMatrix F := by
  have hσ : (σ.permMatrix F)⁻¹ * σ.permMatrix F = 1 := permMatrix_mul_inv σ
  calc
    A⁻¹ = A⁻¹ * 1 := by rw [Matrix.mul_one]
    _ = A⁻¹ * ((σ.permMatrix F)⁻¹ * σ.permMatrix F) := by rw [hσ]
    _ = A⁻¹ * (σ.permMatrix F)⁻¹ * σ.permMatrix F := by rw [← Matrix.mul_assoc]
    _ = (σ.permMatrix F * A)⁻¹ * σ.permMatrix F := by rw [← Matrix.mul_inv_rev]
    _ = (L * U)⁻¹ * σ.permMatrix F := by rw [hLUP]
    _ = U⁻¹ * L⁻¹ * σ.permMatrix F := by rw [Matrix.mul_inv_rev]

end Chapter28

end CLRS
