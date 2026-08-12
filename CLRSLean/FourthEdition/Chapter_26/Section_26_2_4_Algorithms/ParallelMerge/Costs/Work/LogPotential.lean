import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Structure

/-!
# CLRS Chapter 26.3 — P-MERGE Work Potential

This module isolates the natural-logarithm arithmetic that pays for the
binary search performed at every P-MERGE node.  The actual three-quarter
child bound implies that, once the parent is moderately large, both children
retain at least one quarter of its elements up to the removed pivot.
-/

namespace CLRS
namespace Chapter27
namespace ParallelMerge
namespace Costs
namespace Work

/-- The two child logarithms, together with a fixed budget of 64, pay for the
parent's binary-search charge and the change in logarithmic potential.

The small range {lit}`n < 64` is covered by the fixed budget.  Above that
range, {lit}`a + 1` and {lit}`b + 1` are at least {lit}`n / 4`, so each child
logarithm is at least {lit}`log₂ n - 2`.
-/
theorem logPotential_step (a b n : ℕ)
    (hn : 0 < n)
    (hsum : a + b + 1 = n)
    (ha : a ≤ n - n / 4)
    (hb : b ≤ n - n / 4) :
    Nat.log 2 n + 3 + 8 * Nat.log 2 (n + 1) ≤
      64 + 8 * Nat.log 2 (a + 1) + 8 * Nat.log 2 (b + 1) := by
  by_cases hsmall : n < 64
  · have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
    have hlogn : Nat.log 2 n < 6 := by
      apply Nat.log_lt_of_lt_pow hn_ne
      norm_num
      exact hsmall
    have hsucc : n + 1 ≤ 64 := by omega
    have hlogsucc : Nat.log 2 (n + 1) ≤ 6 := by
      calc
        Nat.log 2 (n + 1) ≤ Nat.log 2 64 := Nat.log_monotone hsucc
        _ = 6 := by norm_num
    omega
  · have hn64 : 64 ≤ n := by omega
    have hn_ne : n ≠ 0 := by omega
    have haquarter : n / 4 ≤ a + 1 := by omega
    have hbquarter : n / 4 ≤ b + 1 := by omega
    have hlogdiv : Nat.log 2 (n / 4) = Nat.log 2 n - 2 := by
      simpa using Nat.log_div_base_pow 2 n 2
    have hloga : Nat.log 2 n - 2 ≤ Nat.log 2 (a + 1) := by
      rw [← hlogdiv]
      exact Nat.log_monotone haquarter
    have hlogb : Nat.log 2 n - 2 ≤ Nat.log 2 (b + 1) := by
      rw [← hlogdiv]
      exact Nat.log_monotone hbquarter
    have hlogn : 6 ≤ Nat.log 2 n := by
      calc
        6 = Nat.log 2 64 := by norm_num
        _ ≤ Nat.log 2 n := Nat.log_monotone hn64
    have hlogsucc : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := by
      have hsucc : n + 1 ≤ n * 2 := by omega
      calc
        Nat.log 2 (n + 1) ≤ Nat.log 2 (n * 2) := Nat.log_monotone hsucc
        _ = Nat.log 2 n + 1 := Nat.log_mul_base (by norm_num) hn_ne
    omega

end Work
end Costs
end ParallelMerge
end Chapter27
end CLRS
