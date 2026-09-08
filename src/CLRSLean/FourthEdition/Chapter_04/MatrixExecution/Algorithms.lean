import CLRSLean.FourthEdition.Chapter_04.MatrixExecution.Basic
import CLRSLean.FourthEdition.Chapter_04.Section_04_1_Multiplying_Square_Matrices

/-!
# Matrix multiplication with scalar work

Both algorithms obtain their value and work from the same recursion. Every
matrix sum/difference is itself evaluated by the counted leaf traversal.
Strassen's seven product results are shared; each result is computed and charged
once, even when it contributes to more than one output block.
-/

namespace CLRS.Chapter04.MatrixExecution

/-- Eight recursive products and four counted output-block sums. -/
def mulWithCost (R : Type u) [Ring R] :
    ∀ k, SqMat R k → SqMat R k → Result R k
  | 0, x, y => ⟨x * y, 1⟩
  | k + 1, A, B =>
      let p1 := mulWithCost R k (A 0 0) (B 0 0)
      let p2 := mulWithCost R k (A 0 1) (B 1 0)
      let p3 := mulWithCost R k (A 0 0) (B 0 1)
      let p4 := mulWithCost R k (A 0 1) (B 1 1)
      let p5 := mulWithCost R k (A 1 0) (B 0 0)
      let p6 := mulWithCost R k (A 1 1) (B 1 0)
      let p7 := mulWithCost R k (A 1 0) (B 0 1)
      let p8 := mulWithCost R k (A 1 1) (B 1 1)
      let c11 := zipWithCost R (· + ·) k p1.value p2.value
      let c12 := zipWithCost R (· + ·) k p3.value p4.value
      let c21 := zipWithCost R (· + ·) k p5.value p6.value
      let c22 := zipWithCost R (· + ·) k p7.value p8.value
      ⟨!![c11.value, c12.value; c21.value, c22.value],
        p1.work + p2.work + p3.work + p4.work + p5.work + p6.work + p7.work + p8.work +
        c11.work + c12.work + c21.work + c22.work⟩

/-- Strassen with all ten preparation and eight reassembly sums/differences counted. -/
def strassenWithCost (R : Type u) [Ring R] :
    ∀ k, SqMat R k → SqMat R k → Result R k
  | 0, x, y => ⟨x * y, 1⟩
  | k + 1, A, B =>
      let t1 := zipWithCost R (· - ·) k (B 0 1) (B 1 1)
      let t2 := zipWithCost R (· + ·) k (A 0 0) (A 0 1)
      let t3 := zipWithCost R (· + ·) k (A 1 0) (A 1 1)
      let t4 := zipWithCost R (· - ·) k (B 1 0) (B 0 0)
      let t5 := zipWithCost R (· + ·) k (A 0 0) (A 1 1)
      let t6 := zipWithCost R (· + ·) k (B 0 0) (B 1 1)
      let t7 := zipWithCost R (· - ·) k (A 0 1) (A 1 1)
      let t8 := zipWithCost R (· + ·) k (B 1 0) (B 1 1)
      let t9 := zipWithCost R (· - ·) k (A 0 0) (A 1 0)
      let t10 := zipWithCost R (· + ·) k (B 0 0) (B 0 1)
      let p1 := strassenWithCost R k (A 0 0) t1.value
      let p2 := strassenWithCost R k t2.value (B 1 1)
      let p3 := strassenWithCost R k t3.value (B 0 0)
      let p4 := strassenWithCost R k (A 1 1) t4.value
      let p5 := strassenWithCost R k t5.value t6.value
      let p6 := strassenWithCost R k t7.value t8.value
      let p7 := strassenWithCost R k t9.value t10.value
      let c11a := zipWithCost R (· + ·) k p5.value p4.value
      let c11b := zipWithCost R (· - ·) k c11a.value p2.value
      let c11 := zipWithCost R (· + ·) k c11b.value p6.value
      let c12 := zipWithCost R (· + ·) k p1.value p2.value
      let c21 := zipWithCost R (· + ·) k p3.value p4.value
      let c22a := zipWithCost R (· + ·) k p5.value p1.value
      let c22b := zipWithCost R (· - ·) k c22a.value p3.value
      let c22 := zipWithCost R (· - ·) k c22b.value p7.value
      ⟨!![c11.value, c12.value; c21.value, c22.value],
        t1.work + t2.work + t3.work + t4.work + t5.work + t6.work + t7.work + t8.work +
        t9.work + t10.work + p1.work + p2.work + p3.work + p4.work + p5.work + p6.work +
        p7.work + c11a.work + c11b.work + c11.work + c12.work + c21.work + c22a.work +
        c22b.work + c22.work⟩

/-- Erasing work recovers the existing eight-product algorithm. -/
theorem mulWithCost_value (R : Type u) [Ring R] :
    ∀ (k : Nat) (A B : SqMat R k), (mulWithCost R k A B).value = mulRec R k A B := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      simp only [mulWithCost, addWithCost_value, ih, mulRec]

/-- Erasing work recovers the existing seven-product algorithm. -/
theorem strassenWithCost_value (R : Type u) [Ring R] :
    ∀ (k : Nat) (A B : SqMat R k),
      (strassenWithCost R k A B).value = strassenRec R k A B := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      simp only [strassenWithCost, addWithCost_value, subWithCost_value, ih, strassenRec]

/-- Depth recurrence proved below to be the eight-product execution's work. -/
def mulCount : Nat → Nat
  | 0 => 1
  | k + 1 => 8 * mulCount k + 4 * 4 ^ k

/-- Depth recurrence including Strassen's eighteen block sums/differences. -/
def strassenCount : Nat → Nat
  | 0 => 1
  | k + 1 => 7 * strassenCount k + 18 * 4 ^ k

theorem mulWithCost_work (R : Type u) [Ring R] :
    ∀ (k : Nat) (A B : SqMat R k), (mulWithCost R k A B).work = mulCount k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      simp only [mulWithCost, zipWithCost_work, ih, mulCount]
      omega

theorem strassenWithCost_work (R : Type u) [Ring R] :
    ∀ (k : Nat) (A B : SqMat R k),
      (strassenWithCost R k A B).work = strassenCount k := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro A B
      simp only [strassenWithCost, zipWithCost_work, ih, strassenCount]
      omega

end CLRS.Chapter04.MatrixExecution
