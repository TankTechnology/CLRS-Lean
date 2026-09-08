import CLRSLean.FourthEdition.Chapter_04.Section_04_2_Strassen_Algorithm

/-!
# Scalar-operation execution for block matrices

The counter charges one scalar addition, subtraction, or multiplication.
Matrix addition/subtraction visits all four child blocks recursively; it is not
charged as one scalar operation. Indexing, immutable representation, allocation,
and forming the four output blocks are outside this arithmetic model. Local
results are shared when a later expression uses them more than once.
-/

namespace CLRS.Chapter04.MatrixExecution

/-- A returned matrix and the scalar arithmetic operations used to obtain it. -/
structure Result (R : Type u) (k : Nat) where
  value : SqMat R k
  work : Nat

/-- Apply one scalar operation at every corresponding pair of leaves. -/
def zipWithCost (R : Type u) (op : R → R → R) :
    ∀ k, SqMat R k → SqMat R k → Result R k
  | 0, x, y => ⟨op x y, 1⟩
  | k + 1, A, B =>
      let a := zipWithCost R op k (A 0 0) (B 0 0)
      let b := zipWithCost R op k (A 0 1) (B 0 1)
      let c := zipWithCost R op k (A 1 0) (B 1 0)
      let d := zipWithCost R op k (A 1 1) (B 1 1)
      ⟨!![a.value, b.value; c.value, d.value], a.work + b.work + c.work + d.work⟩

/-- The count comes from visiting the scalar leaves of the returned matrix. -/
theorem zipWithCost_work (R : Type u) (op : R → R → R) :
    ∀ (k : Nat) (A B : SqMat R k), (zipWithCost R op k A B).work = 4 ^ k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      simp only [zipWithCost, ih, pow_succ]
      omega

theorem addWithCost_value (R : Type u) [Ring R] :
    ∀ (k : Nat) (A B : SqMat R k),
      (zipWithCost R (· + ·) k A B).value = A + B := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      funext i j
      fin_cases i <;> fin_cases j <;> simp [zipWithCost, ih] <;> rfl

theorem subWithCost_value (R : Type u) [Ring R] :
    ∀ (k : Nat) (A B : SqMat R k),
      (zipWithCost R (· - ·) k A B).value = A - B := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      funext i j
      fin_cases i <;> fin_cases j <;> simp [zipWithCost, ih] <;> rfl

end CLRS.Chapter04.MatrixExecution
