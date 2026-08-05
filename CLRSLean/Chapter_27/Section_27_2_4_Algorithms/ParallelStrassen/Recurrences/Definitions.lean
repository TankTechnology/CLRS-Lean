import Mathlib.Tactic

/-!
# Chapter 27 extension — parallel Strassen recurrences: definitions

This compatibility extension records the work/span recurrences and their exact
power-of-two solutions for the parallelized form of Strassen's algorithm.
It is deliberately separated from the Chapter 27 main-text recurrences.
-/

namespace CLRS
namespace Chapter27

private theorem pow_two_succ_eq (k : ℕ) : 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  omega

private theorem two_le_two_pow_succ (k : ℕ) : 2 ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow k 2 (by norm_num)
  omega

private theorem two_pow_succ_mul (k : ℕ) : 2 ^ (k + 1) * 2 ^ (k + 1) = 4 ^ (k + 1) := by
  have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h42, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- Work recurrence for parallel Strassen: `T₁(n) = 7 T₁(n/2) + n²`. -/
def strassenWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    7 * strassenWork (n / 2) + n * n
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem strassenWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    strassenWork n = 7 * strassenWork (n / 2) + n * n := by
  rw [strassenWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact work on powers of two: `3·T₁(2ᵏ) + 4ᵏ⁺¹ = 7ᵏ⁺¹`
(work `Θ(n^(log₂ 7))`). -/
theorem strassenWork_pow_two (k : ℕ) :
    3 * strassenWork (2 ^ k) + 4 ^ (k + 1) = 7 ^ (k + 1) := by
  induction k with
  | zero =>
      rw [strassenWork]
      norm_num
  | succ k ih =>
      rw [strassenWork_unfold (two_le_two_pow_succ k), pow_two_succ_eq,
        two_pow_succ_mul]
      nlinarith [ih, pow_succ (4 : ℕ) (k + 1), pow_succ (7 : ℕ) (k + 1)]

/-- Span recurrence for parallel Strassen: `T∞(n) = T∞(n/2) + 1`. -/
def strassenSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    n
  else
    strassenSpan (n / 2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

theorem strassenSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    strassenSpan n = strassenSpan (n / 2) + 1 := by
  rw [strassenSpan]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span on powers of two: `T∞(2ᵏ) = k + 1` (span `Θ(log n)`). -/
theorem strassenSpan_pow_two (k : ℕ) : strassenSpan (2 ^ k) = k + 1 := by
  induction k with
  | zero =>
      rw [strassenSpan]
      norm_num
  | succ k ih =>
      rw [strassenSpan_unfold (two_le_two_pow_succ k), pow_two_succ_eq, ih]

end Chapter27
end CLRS
