import Mathlib.Tactic

/-!
# 4.3. The Substitution Method

This file packages the CLRS substitution method as reusable induction
principles for one-step recurrence bounds.  The core idea is intentionally
small: a guessed bound is a loop invariant over the recurrence index.

Main results:

- Theorem {lit}`CLRS.Chapter04.substitution_upper_bound`: base plus step
  preservation proves an upper bound.
- Theorem {lit}`CLRS.Chapter04.substitution_lower_bound`: the corresponding
  lower-bound principle.
- Theorem {lit}`CLRS.Chapter04.substitution_sandwich`: simultaneous lower and
  upper bounds.
- Theorems {lit}`CLRS.Chapter04.linear_substitution_upper_bound` and
  {lit}`CLRS.Chapter04.geometric_substitution_upper_bound`: ready-to-use
  CLRS-style templates for common recurrence guesses.

Status: `proved` for the substitution-method induction principles.
Later divide-and-conquer sections instantiate these templates.
-/

namespace CLRS
namespace Chapter04

/-- A proposed upper bound for a cost function. -/
def IsUpperBound (T B : ℕ → ℝ) : Prop := ∀ n, T n ≤ B n

/-- A proposed lower bound for a cost function. -/
def IsLowerBound (T B : ℕ → ℝ) : Prop := ∀ n, B n ≤ T n

/--
The basic substitution-method upper-bound principle: prove the proposed bound
at the base case, then prove that one recurrence step preserves it.
-/
theorem substitution_upper_bound (T B : ℕ → ℝ)
    (h0 : T 0 ≤ B 0)
    (hstep : ∀ n, T n ≤ B n → T (n + 1) ≤ B (n + 1)) :
    IsUpperBound T B := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hstep n ih

/--
The lower-bound form of the substitution method.  It has the same proof shape
as the upper-bound theorem, but the guessed function is below the recurrence.
-/
theorem substitution_lower_bound (T B : ℕ → ℝ)
    (h0 : B 0 ≤ T 0)
    (hstep : ∀ n, B n ≤ T n → B (n + 1) ≤ T (n + 1)) :
    IsLowerBound T B := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hstep n ih

/--
If the lower and upper guesses are both preserved by the recurrence step, then
the true cost function is sandwiched between them for every index.
-/
theorem substitution_sandwich (T L U : ℕ → ℝ)
    (hL0 : L 0 ≤ T 0)
    (hU0 : T 0 ≤ U 0)
    (hLstep : ∀ n, L n ≤ T n → L (n + 1) ≤ T (n + 1))
    (hUstep : ∀ n, T n ≤ U n → T (n + 1) ≤ U (n + 1)) :
    IsLowerBound T L ∧ IsUpperBound T U := by
  constructor
  · exact substitution_lower_bound T L hL0 hLstep
  · exact substitution_upper_bound T U hU0 hUstep

/-! ## Common recurrence templates -/

/--
Linear additive upper bounds: if each step adds at most {lit}`inc`, then the
cost is at most the base bound plus {lit}`inc * n`.
-/
theorem linear_substitution_upper_bound (T : ℕ → ℝ) {base inc : ℝ}
    (h0 : T 0 ≤ base)
    (hstep : ∀ n, T (n + 1) ≤ T n + inc) :
    ∀ n : ℕ, T n ≤ base + inc * (n : ℝ) := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        T (n + 1) ≤ T n + inc := hstep n
        _ ≤ (base + inc * (n : ℝ)) + inc := by linarith
        _ = base + inc * ((n + 1 : ℕ) : ℝ) := by
          norm_num
          ring

/--
Linear additive lower bounds: if each step adds at least {lit}`inc`, then the
cost is at least the base bound plus {lit}`inc * n`.
-/
theorem linear_substitution_lower_bound (T : ℕ → ℝ) {base inc : ℝ}
    (h0 : base ≤ T 0)
    (hstep : ∀ n, T n + inc ≤ T (n + 1)) :
    ∀ n : ℕ, base + inc * (n : ℝ) ≤ T n := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        base + inc * ((n + 1 : ℕ) : ℝ) = (base + inc * (n : ℝ)) + inc := by
          norm_num
          ring
        _ ≤ T n + inc := by linarith
        _ ≤ T (n + 1) := hstep n

/--
Geometric upper bounds: a nonnegative multiplicative step preserves a guessed
bound of the form {lit}`base * a^n`.
-/
theorem geometric_substitution_upper_bound (T : ℕ → ℝ) {base a : ℝ}
    (ha_nonneg : 0 ≤ a)
    (h0 : T 0 ≤ base)
    (hstep : ∀ n, T (n + 1) ≤ a * T n) :
    ∀ n : ℕ, T n ≤ base * a ^ n := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        T (n + 1) ≤ a * T n := hstep n
        _ ≤ a * (base * a ^ n) := by
          gcongr
        _ = base * a ^ (n + 1) := by
          rw [pow_succ]
          ring

/--
Geometric lower bounds, dual to
{lit}`CLRS.Chapter04.geometric_substitution_upper_bound`.
-/
theorem geometric_substitution_lower_bound (T : ℕ → ℝ) {base a : ℝ}
    (ha_nonneg : 0 ≤ a)
    (h0 : base ≤ T 0)
    (hstep : ∀ n, a * T n ≤ T (n + 1)) :
    ∀ n : ℕ, base * a ^ n ≤ T n := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      calc
        base * a ^ (n + 1) = a * (base * a ^ n) := by
          rw [pow_succ]
          ring
        _ ≤ a * T n := by
          gcongr
        _ ≤ T (n + 1) := hstep n

end Chapter04
end CLRS
