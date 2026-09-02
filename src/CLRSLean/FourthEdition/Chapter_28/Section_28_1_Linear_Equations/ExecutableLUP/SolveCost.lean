import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP.Cost

/-!
# CLRS Section 28.1 - Costed LUP-SOLVE

Forward and backward substitution carry counters produced by the same
dimension recursion as their returned vectors.
-/

namespace CLRS
namespace Chapter28

open Matrix

variable {F : Type} [Field F]

/-- Vector result with exact-algebra field-operation work. -/
structure VectorExecution (n : Nat) (F : Type) where
  value : Fin n → F
  work : Nat

/-- Costed forward substitution.  Each trailing right-hand-side entry charges
one multiplication and one subtraction. -/
def forwardSubstWithCost : ∀ {n : Nat},
    Matrix (Fin n) (Fin n) F → (Fin n → F) → VectorExecution n F
  | 0, _L, _b => ⟨fun i => Fin.elim0 i, 0⟩
  | n + 1, L, b =>
      let L2 : Matrix (Fin n) (Fin n) F := fun i j => L (Fin.succ i) (Fin.succ j)
      let b2 : Fin n → F := fun i => b (Fin.succ i) - L (Fin.succ i) 0 * b 0
      let tail := forwardSubstWithCost L2 b2
      ⟨Fin.cons (b 0) tail.value, tail.work + 2 * n⟩

/-- Costed backward substitution.  A level charges one pivot division plus the
two field operations used to update each leading right-hand-side entry. -/
def backSubstWithCost : ∀ {n : Nat},
    Matrix (Fin n) (Fin n) F → (Fin n → F) → VectorExecution n F
  | 0, _U, _y => ⟨fun i => Fin.elim0 i, 0⟩
  | n + 1, U, y =>
      let last : Fin (n + 1) := Fin.last n
      let U1 : Matrix (Fin n) (Fin n) F := fun i j => U (Fin.castSucc i) (Fin.castSucc j)
      let xl : F := y last / U last last
      let y1 : Fin n → F := fun i => y (Fin.castSucc i) - U (Fin.castSucc i) last * xl
      let head := backSubstWithCost U1 y1
      ⟨Fin.snoc head.value xl, head.work + 2 * n + 1⟩

theorem forwardSubstWithCost_value : ∀ {n : Nat}
    (L : Matrix (Fin n) (Fin n) F) (b : Fin n → F),
    (forwardSubstWithCost L b).value = forwardSubst L b
  | 0, _L, _b => by
      funext i
      exact Fin.elim0 i
  | n + 1, L, b => by
      simp [forwardSubstWithCost, forwardSubst, forwardSubstWithCost_value]

theorem backSubstWithCost_value : ∀ {n : Nat}
    (U : Matrix (Fin n) (Fin n) F) (y : Fin n → F),
    (backSubstWithCost U y).value = backSubst U y
  | 0, _U, _y => by
      funext i
      exact Fin.elim0 i
  | n + 1, U, y => by
      simp [backSubstWithCost, backSubst, backSubstWithCost_value]

theorem forwardSubstWithCost_work_le : ∀ {n : Nat}
    (L : Matrix (Fin n) (Fin n) F) (b : Fin n → F),
    (forwardSubstWithCost L b).work ≤ n ^ 2
  | 0, _L, _b => by simp [forwardSubstWithCost]
  | n + 1, L, b => by
      let L2 : Matrix (Fin n) (Fin n) F := fun i j => L (Fin.succ i) (Fin.succ j)
      let b2 : Fin n → F := fun i => b (Fin.succ i) - L (Fin.succ i) 0 * b 0
      have ih := forwardSubstWithCost_work_le L2 b2
      simp only [forwardSubstWithCost]
      change (forwardSubstWithCost L2 b2).work + 2 * n ≤ (n + 1) ^ 2
      simp [pow_two]
      nlinarith

theorem backSubstWithCost_work_le : ∀ {n : Nat}
    (U : Matrix (Fin n) (Fin n) F) (y : Fin n → F),
    (backSubstWithCost U y).work ≤ n ^ 2
  | 0, _U, _y => by simp [backSubstWithCost]
  | n + 1, U, y => by
      let last : Fin (n + 1) := Fin.last n
      let U1 : Matrix (Fin n) (Fin n) F := fun i j => U (Fin.castSucc i) (Fin.castSucc j)
      let xl : F := y last / U last last
      let y1 : Fin n → F := fun i => y (Fin.castSucc i) - U (Fin.castSucc i) last * xl
      have ih := backSubstWithCost_work_le U1 y1
      simp only [backSubstWithCost]
      change (backSubstWithCost U1 y1).work + 2 * n + 1 ≤ (n + 1) ^ 2
      simp [pow_two]
      nlinarith

/-- Apply a permutation to a vector by direct index lookup.  This is the
zero-field-operation implementation of multiplication by a permutation
matrix. -/
def permuteVector {n : Nat} (σ : Equiv.Perm (Fin n)) (b : Fin n → F) : Fin n → F :=
  b ∘ σ

theorem permuteVector_eq_permMatrix_mulVec {n : Nat} (σ : Equiv.Perm (Fin n))
    (b : Fin n → F) :
    permuteVector σ b = σ.permMatrix F *ᵥ b := by
  simpa [permuteVector] using (Matrix.permMatrix_mulVec (σ := σ) (v := b)).symm

/-- Costed LUP-SOLVE, including the direct permutation and both triangular
substitutions. -/
def lupSolveWithCost {n : Nat} (σ : Equiv.Perm (Fin n))
    (L U : Matrix (Fin n) (Fin n) F) (b : Fin n → F) : VectorExecution n F :=
  let forward := forwardSubstWithCost L (permuteVector σ b)
  let backward := backSubstWithCost U forward.value
  ⟨backward.value, forward.work + backward.work⟩

/-- Erasing the solver counter gives the existing `lupSolve`. -/
theorem lupSolveWithCost_value {n : Nat} (σ : Equiv.Perm (Fin n))
    (L U : Matrix (Fin n) (Fin n) F) (b : Fin n → F) :
    (lupSolveWithCost σ L U b).value = lupSolve σ L U b := by
  rw [lupSolveWithCost]
  simp only
  rw [backSubstWithCost_value, forwardSubstWithCost_value]
  rw [permuteVector_eq_permMatrix_mulVec]
  rfl

/-- The actual two-substitution execution uses at most `2n²` field
operations. -/
theorem lupSolveWithCost_work_le {n : Nat} (σ : Equiv.Perm (Fin n))
    (L U : Matrix (Fin n) (Fin n) F) (b : Fin n → F) :
    (lupSolveWithCost σ L U b).work ≤ 2 * n ^ 2 := by
  rw [lupSolveWithCost]
  simp only
  have hf := forwardSubstWithCost_work_le L (permuteVector σ b)
  have hb := backSubstWithCost_work_le U
    (forwardSubstWithCost L (permuteVector σ b)).value
  omega

/-- The costed solver returns the same certified solution as `lupSolve`. -/
theorem lupSolveWithCost_correct {n : Nat}
    {A L U : Matrix (Fin n) (Fin n) F} {σ : Equiv.Perm (Fin n)}
    (hLUP : σ.permMatrix F * A = L * U) (hL : IsUnitLowerTriangular L)
    (hU : IsUpperTriangular U) (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (b : Fin n → F) :
    A *ᵥ (lupSolveWithCost σ L U b).value = b := by
  rw [lupSolveWithCost_value]
  exact lupSolve_correct hLUP hL hU hdiag b

end Chapter28
end CLRS
