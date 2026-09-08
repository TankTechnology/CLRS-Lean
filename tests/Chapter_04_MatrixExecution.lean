import CLRSLean.FourthEdition.Chapter_04

open CLRS.Chapter04
#check MatrixExecution.mulWithCost_value
#check MatrixExecution.strassenWithCost_value
#check MatrixExecution.mulWithCost_work_eq
#check MatrixExecution.strassenWithCost_work_bounds
#check MatrixExecution.mulWithCost_correct
#check MatrixExecution.strassenWithCost_correct

open MatrixExecution

-- A nonsymmetric product checks both placement and subtraction signs.
private def A : SqMat Int 1 := !![1, 2; 3, 4]
private def B : SqMat Int 1 := !![5, 6; 7, 8]

example : (mulWithCost Int 1 A B).value = !![19, 22; 43, 50] := by rfl
example : (strassenWithCost Int 1 A B).value = !![19, 22; 43, 50] := by rfl
example : (mulWithCost Int 1 A B).work = 12 := by decide
example : (strassenWithCost Int 1 A B).work = 25 := by decide

-- The scalar base counts one multiplication, including zero-valued inputs.
example : (strassenWithCost Int 0 0 7).value = 0 ∧
    (strassenWithCost Int 0 0 7).work = 1 := by constructor <;> rfl

-- A further block level must charge all scalar entries of each block sum.
example : (mulWithCost Int 2 (padOne Int 1 A) (padOne Int 1 B)).work = 112 := by
  rw [mulWithCost_work]; decide
example : (strassenWithCost Int 2 (padOne Int 1 A) (padOne Int 1 B)).work = 247 := by
  rw [strassenWithCost_work]; decide

-- Correctness requires a ring, not commutativity of multiplication.
example (R : Type*) [Ring R] (k : Nat) (X Y : SqMat R k) :
    (strassenWithCost R k X Y).value = X * Y :=
  (strassenWithCost_correct R k X Y).1

-- Public asymptotics read the returned work on every input family.
example (R : Type*) [Ring R] (X Y : ∀ k, SqMat R k) :
    CLRS.Chapter03.isBigTheta (fun k => ((mulWithCost R k (X k) (Y k)).work : ℝ))
      (fun k => ((2 ^ k : Nat) : ℝ) ^ 3) := mulWithCost_theta R X Y

example (R : Type*) [Ring R] (X Y : ∀ k, SqMat R k) :
    CLRS.Chapter03.isBigTheta (fun k => ((strassenWithCost R k (X k) (Y k)).work : ℝ))
      (fun k => ((2 ^ k : Nat) : ℝ) ^ Real.logb 2 7) := strassenWithCost_theta R X Y
