import CLRSLean.FourthEdition.Chapter_04.MatrixExecution.Bounds

/-!
# Asymptotic scalar work on power-of-two squares

The functions below read counters from arbitrary families of input matrices.
The asymptotic variable is depth k; the comparison functions use their actual
side length 2^k. Consequently these statements do not extend the input type to
all natural dimensions.
-/

namespace CLRS.Chapter04.MatrixExecution

private theorem cubic_side (k : Nat) : ((2 ^ k : Nat) : ℝ) ^ 3 = (8 : ℝ) ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm k 3, pow_mul]
  norm_num

private theorem strassen_side (k : Nat) :
    ((2 ^ k : Nat) : ℝ) ^ Real.logb 2 7 = (7 : ℝ) ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num)]
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-- Every input family has cubic scalar work in its power-of-two side length. -/
theorem mulWithCost_theta (R : Type u) [Ring R] (A B : ∀ k, SqMat R k) :
    Chapter03.isBigTheta (fun k => ((mulWithCost R k (A k) (B k)).work : ℝ))
      (fun k => ((2 ^ k : Nat) : ℝ) ^ 3) := by
  constructor
  · rw [Chapter03.isBigO_iff]
    refine ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [mulWithCost_work, cubic_side, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    exact_mod_cast (mulCount_bounds k).2
  · rw [Chapter03.isBigOmega_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [mulWithCost_work, cubic_side, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    exact_mod_cast (mulCount_bounds k).1

/-- Every input family has Strassen's scalar-work exponent on its side length. -/
theorem strassenWithCost_theta (R : Type u) [Ring R] (A B : ∀ k, SqMat R k) :
    Chapter03.isBigTheta (fun k => ((strassenWithCost R k (A k) (B k)).work : ℝ))
      (fun k => ((2 ^ k : Nat) : ℝ) ^ Real.logb 2 7) := by
  constructor
  · rw [Chapter03.isBigO_iff]
    refine ⟨7, by norm_num, 0, ?_⟩
    intro k _
    rw [strassenWithCost_work, strassen_side, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    exact_mod_cast (strassenCount_bounds k).2
  · rw [Chapter03.isBigOmega_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [strassenWithCost_work, strassen_side, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    exact_mod_cast (strassenCount_bounds k).1

end CLRS.Chapter04.MatrixExecution
