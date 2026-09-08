import CLRSLean.FourthEdition.Chapter_04.MatrixExecution.Algorithms

/-!
# Bounds for executed scalar arithmetic

These results concern matrices of side length 2^k. The eight-product counter
equals the existing work recurrence on that domain. Strassen's eighteen block
sums give a different exact count, bounded by constant multiples of the
existing recurrence. Neither result claims an arbitrary-dimension padding API
or a machine-time bound for ring operations of nonconstant cost.
-/

namespace CLRS.Chapter04.MatrixExecution

private theorem side_square (k : Nat) : ((2 ^ k : Nat) : ℝ) ^ 2 = (4 ^ k : Nat) := by
  norm_cast
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
  norm_num

theorem mulCount_eq_budget (k : Nat) : (mulCount k : ℝ) = mulWork (2 ^ k) := by
  induction k with
  | zero => simp [mulCount, mulWork_one]
  | succ k ih =>
      rw [mulCount, Nat.cast_add, Nat.cast_mul, ih,
        mulWork_pos_step (2 ^ (k + 1)) (by positivity)]
      have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
      rw [hdiv, side_square]
      simp only [pow_succ 4 k,
        Nat.cast_mul, Nat.cast_ofNat]
      norm_num
      ring

theorem strassenCount_budget_bounds (k : Nat) :
    strassenWork (2 ^ k) ≤ (strassenCount k : ℝ) ∧
      (strassenCount k : ℝ) ≤ 5 * strassenWork (2 ^ k) := by
  induction k with
  | zero => norm_num [strassenCount, strassenWork_one]
  | succ k ih =>
      rw [strassenCount, Nat.cast_add, Nat.cast_mul,
        strassenWork_pos_step (2 ^ (k + 1)) (by positivity)]
      have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
      rw [hdiv, side_square]
      simp only [pow_succ 4 k,
        Nat.cast_mul, Nat.cast_ofNat]
      have hnonneg : (0 : ℝ) ≤ (4 ^ k : Nat) := by positivity
      constructor <;> nlinarith [ih.1, ih.2]

/-- Equality with the budget is proved from the returned execution counter. -/
theorem mulWithCost_work_eq (R : Type u) [Ring R] (k : Nat) (A B : SqMat R k) :
    ((mulWithCost R k A B).work : ℝ) = mulWork (2 ^ k) := by
  rw [mulWithCost_work, mulCount_eq_budget]

/-- Strassen's actual arithmetic count is within a factor of five of the budget. -/
theorem strassenWithCost_work_bounds (R : Type u) [Ring R]
    (k : Nat) (A B : SqMat R k) :
    strassenWork (2 ^ k) ≤ ((strassenWithCost R k A B).work : ℝ) ∧
      ((strassenWithCost R k A B).work : ℝ) ≤ 5 * strassenWork (2 ^ k) := by
  rw [strassenWithCost_work]
  exact strassenCount_budget_bounds k

theorem mulCount_closed (k : Nat) : mulCount k + 4 ^ k = 2 * 8 ^ k := by
  induction k with
  | zero => norm_num [mulCount]
  | succ k ih => simp only [mulCount, pow_succ]; omega

theorem strassenCount_closed (k : Nat) : strassenCount k + 6 * 4 ^ k = 7 * 7 ^ k := by
  induction k with
  | zero => norm_num [strassenCount]
  | succ k ih => simp only [strassenCount, pow_succ]; omega

theorem mulCount_bounds (k : Nat) : 8 ^ k ≤ mulCount k ∧ mulCount k ≤ 2 * 8 ^ k := by
  have h := mulCount_closed k
  have hpow : 4 ^ k ≤ 8 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hnonneg := Nat.zero_le (4 ^ k)
  omega

theorem strassenCount_bounds (k : Nat) :
    7 ^ k ≤ strassenCount k ∧ strassenCount k ≤ 7 * 7 ^ k := by
  have h := strassenCount_closed k
  have hpow : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by norm_num) k
  omega

/-- Value correctness and work for the same eight-product run. -/
theorem mulWithCost_correct (R : Type u) [Ring R] (k : Nat) (A B : SqMat R k) :
    (mulWithCost R k A B).value = A * B ∧
      ((mulWithCost R k A B).work : ℝ) = mulWork (2 ^ k) :=
  ⟨by rw [mulWithCost_value, mulRec_correct], mulWithCost_work_eq R k A B⟩

/-- Value correctness and work bounds for the same seven-product run. -/
theorem strassenWithCost_correct (R : Type u) [Ring R] (k : Nat) (A B : SqMat R k) :
    (strassenWithCost R k A B).value = A * B ∧
      strassenWork (2 ^ k) ≤ ((strassenWithCost R k A B).work : ℝ) ∧
      ((strassenWithCost R k A B).work : ℝ) ≤ 5 * strassenWork (2 ^ k) :=
  ⟨by rw [strassenWithCost_value, strassenRec_correct], strassenWithCost_work_bounds R k A B⟩

end CLRS.Chapter04.MatrixExecution
