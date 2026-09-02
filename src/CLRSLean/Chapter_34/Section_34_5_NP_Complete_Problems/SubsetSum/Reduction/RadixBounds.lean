import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Construction

/-!
# Power-of-two radix bounds for the SUBSET-SUM reduction

The reduction reserves one block of `reductionBlockWidth` bits per textbook
column.  These elementary inequalities isolate the only arithmetic needed to
show that neither selected item sums nor the target digit can carry into the
next block.
-/

namespace CLRS.Chapter34.SubsetSumReduction

theorem three_mul_lt_two_pow_add_three (count : Nat) :
    3 * count < 2 ^ (count + 3) := by
  have hcount : count < 2 ^ count := count.lt_two_pow_self
  have hscaled : 3 * count < 3 * 2 ^ count := by
    omega
  have hcoeff : 3 * 2 ^ count ≤ 8 * 2 ^ count := by
    exact Nat.mul_le_mul_right (2 ^ count) (by omega)
  calc
    3 * count < 3 * 2 ^ count := hscaled
    _ ≤ 8 * 2 ^ count := hcoeff
    _ = 2 ^ (count + 3) := by simp [pow_add, Nat.mul_comm]

theorem four_lt_two_pow_add_three (count : Nat) :
    4 < 2 ^ (count + 3) := by
  have hmono : 2 ^ 3 ≤ 2 ^ (count + 3) := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  norm_num at hmono ⊢
  omega

@[simp] theorem reductionBase_eq_pow (formula : CNF) :
    reductionBase formula = 2 ^ reductionBlockWidth formula := rfl

theorem reductionBlockWidth_pos (formula : CNF) :
    0 < reductionBlockWidth formula := by
  simp [reductionBlockWidth]

theorem reductionBase_pos (formula : CNF) :
    0 < reductionBase formula := by
  simp [reductionBase]

theorem three_mul_reductionItems_card_lt_base (formula : CNF) :
    3 * (reductionItems formula).card < reductionBase formula := by
  simpa [reductionBase, reductionBlockWidth] using
    three_mul_lt_two_pow_add_three (reductionItems formula).card

theorem four_lt_reductionBase (formula : CNF) :
    4 < reductionBase formula := by
  simpa [reductionBase, reductionBlockWidth] using
    four_lt_two_pow_add_three (reductionItems formula).card

end CLRS.Chapter34.SubsetSumReduction
