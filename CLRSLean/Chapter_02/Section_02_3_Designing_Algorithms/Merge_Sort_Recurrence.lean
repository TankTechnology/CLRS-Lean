import Mathlib
import CLRSLean.Chapter_02.Section_02_3_Designing_Algorithms
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_04.Section_04_5_Master_Theorem
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input

/-!
# CLRS §2.3 — Merge Sort Recurrence and Θ(n log n) Bound

This file formalizes the merge sort recurrence from CLRS §2.3:

> T(n) = T(⌊n/2⌋) + T(⌈n/2⌉) + Θ(n)

and proves the tight asymptotic bound T(n) = Θ(n log n) for **all** input
sizes.  The exact-power bound `T(2^i) = Θ((i+1)·2^i)` comes from the Master
Theorem; `theta_n_log_n_all_inputs` extends it to every natural input through
the Chapter 4 §4.6 floor/ceiling sandwich bridge.

## Approach

The recurrence is stated for arbitrary input sizes using natural-number
floor/ceiling division.  On exact powers of two (n = 2^k) the recurrence
collapses to the standard divide-and-conquer form

> T(2^(k+1)) = 2·T(2^k) + 2^(k+1),

which is exactly the Master Theorem pattern with a = b = 2 and f(n) = n.
The Chapter 4 Master Theorem (case 2: constant normalized forcing) then
yields T(2^k) = Θ((k+1)·2^k), i.e. T(n) = Θ(n log n).

We intentionally place this material in a separate sub-namespace
`CLRS.Chapter02.MergeSortRecurrence` to avoid name conflicts with the
existing `mergeSort` definition and its correctness theorems in
`CLRS.Chapter02` (Section_02_3_Designing_Algorithms.lean).

## References

* The verified merge sort implementation: `CLRS.Chapter02.mergeSort`
* The power-of-two closed form: `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`
* The Master Theorem: `CLRS.Chapter04.master_case2_constant_forcing`
-/

namespace CLRS
namespace Chapter02
namespace MergeSortRecurrence

/-! ### The recurrence relation -/

/--
The merge sort recurrence from CLRS §2.3, expressed for an arbitrary
cost function `T : ℕ → ℝ`.

For n ≥ 2:
  T(n) = T(⌊n/2⌋) + T(⌈n/2⌉) + n

Natural-number division `n / 2` gives `⌊n/2⌋` and `(n+1) / 2` gives
`⌈n/2⌉`.  The additive term `(n : ℝ)` stands for the linear-time merge
step; the Θ-annotation absorbs constant factors that are irrelevant
for the asymptotic analysis.

Base cases T(0) and T(1) are left unspecified by this predicate —
clients supply them when instantiating a concrete cost function.
-/
def Recurrence (T : ℕ → ℝ) : Prop :=
  ∀ n, 2 ≤ n → T n = T (n / 2) + T ((n + 1) / 2) + (n : ℝ)

/-! ### Reduction to the Master Theorem form on exact powers -/

/--
On exact powers of two, the merge sort recurrence simplifies to the
standard divide-and-conquer equation required by the Master Theorem.

For n = 2^(k+1) we have n/2 = (n+1)/2 = 2^k, so the two recursive
calls merge into one doubled term.
-/
theorem recurrence_on_exact_power (T : ℕ → ℝ) (hRec : Recurrence T) (k : ℕ) :
    T (2 ^ (k + 1)) = (2 : ℝ) * T (2 ^ k) + ((2 ^ (k + 1) : ℕ) : ℝ) := by
  have hn : 2 ≤ 2 ^ (k + 1) := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ k + 1)
  have h := hRec (2 ^ (k + 1)) hn
  have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by omega
  have hceil : (2 ^ (k + 1) + 1) / 2 = 2 ^ k := by omega
  simp [hdiv, hceil] at h
  simpa [two_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using h

/--
The merge sort recurrence on exact powers satisfies the Chapter 4
`ExactPowerRecurrence` structure with a = 2, b = 2, f(n) = n.
-/
theorem exactPowerRecurrence_instance (T : ℕ → ℝ) (hRec : Recurrence T) :
    Chapter04.ExactPowerRecurrence 2 2 (fun n : ℕ => (n : ℝ)) T :=
  ⟨fun i => by
    simpa [Nat.cast_pow] using recurrence_on_exact_power T hRec i⟩

/-! ### Θ(n log n) bound via the Master Theorem -/

/--
The normalized forcing term for merge sort is identically 1.

With a = b = 2 and f(n) = n, we have

  f(b^(k+1)) / a^(k+1) = 2^(k+1) / 2^(k+1) = 1.

This means the Master Theorem's case 2 applies: the forcing is
trapped between positive constants (here, exactly 1), giving
T(2^k) = Θ((k+1)·2^k).
-/
lemma normalizedForcing_merge_sort (k : ℕ) :
    Chapter04.normalizedForcing 2 2 (fun n : ℕ => (n : ℝ)) k = (1 : ℝ) := by
  dsimp [Chapter04.normalizedForcing]
  simp [Nat.cast_pow]

/--
Merge sort runs in Θ(n log n) time on exact powers of two.

Formally, for any cost function T satisfying the textbook recurrence
with T(1) > 0 and nonnegative values, the sequence n ↦ T(2^k) is
Θ(k ↦ (k+1)·2^k).  Since 2^k = n and k = log₂ n, this is exactly
the textbook statement T(n) = Θ(n log n).
-/
theorem theta_n_log_n_on_exact_powers (T : ℕ → ℝ) (hRec : Recurrence T)
    (hT1 : 0 < T 1) :
    Chapter03.isBigTheta
      (fun k : ℕ => T (2 ^ k))
      (fun k : ℕ => ((k : ℝ) + 1) * ((2 : ℝ) ^ k)) := by
  have h_rec_mt : Chapter04.ExactPowerRecurrence 2 2 (fun n : ℕ => (n : ℝ)) T :=
    exactPowerRecurrence_instance T hRec
  have ha_pos : 0 < (2 : ℝ) := by norm_num
  have h_base_nonneg : 0 ≤ Chapter04.normalizedValue 2 2 T 0 := by
    simpa [Chapter04.normalizedValue] using hT1.le
  have h_forcing_eq (k : ℕ) : Chapter04.normalizedForcing 2 2 (fun n : ℕ => (n : ℝ)) k = (1 : ℝ) :=
    normalizedForcing_merge_sort k
  have h_term_lower : ∀ k, (1 : ℝ) ≤ Chapter04.normalizedForcing 2 2 (fun n : ℕ => (n : ℝ)) k := by
    intro k; rw [h_forcing_eq k]
  have h_term_upper : ∀ k, Chapter04.normalizedForcing 2 2 (fun n : ℕ => (n : ℝ)) k ≤ (1 : ℝ) := by
    intro k; rw [h_forcing_eq k]
  exact Chapter04.master_case2_constant_forcing 2 2 (fun n : ℕ => (n : ℝ)) T
    h_rec_mt ha_pos h_base_nonneg (by norm_num) (by norm_num) h_term_lower h_term_upper

/-! ### All-input Θ(n log n) bound -/

/-- On an exact power of two the discrete case-2 scale
`(⌊log₂ n⌋ + 1)·2^(⌊log₂ n⌋)` collapses to `(i+1)·2^i`. -/
lemma exactPower_scale_eq_criticalPowerLogScale (i : ℕ) :
    ((i : ℝ) + 1) * ((2 : ℝ) ^ i) = Chapter04.criticalPowerLogScale 2 2 (2 ^ i) := by
  rw [Chapter04.criticalPowerLogScale_exactPower 2 2 i (by norm_num : (1 : ℕ) < 2)]
  norm_num

/-- For `a = b = 2` the textbook case-2 scale `n^(log₂2)·log n` is exactly
`n·log n`. -/
lemma realLogLogScale_two_two (n : ℕ) :
    Chapter04.realLogLogScale 2 2 n = (n : ℝ) * Real.log (n : ℝ) := by
  unfold Chapter04.realLogLogScale Chapter04.realLogScale Chapter04.realLogExponent
  have hlog2_pos : 0 < Real.log ((2 : ℕ) : ℝ) := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < ((2 : ℕ) : ℝ))
  have hlog2_ne : Real.log ((2 : ℕ) : ℝ) ≠ 0 := ne_of_gt hlog2_pos
  have hexp : Real.log ((2 : ℕ) : ℝ) / Real.log ((2 : ℕ) : ℝ) = 1 := by
    rw [div_self hlog2_ne]
  rw [hexp]
  simp

/--
**Merge sort is Θ(n log n) for all input sizes** (CLRS §2.3).

For any cost function `T` satisfying the merge-sort recurrence on every input,
with `T(1) > 0` and `T` monotone in absolute value, `T` is Θ(n·log n).

This extends `theta_n_log_n_on_exact_powers` from exact powers of two to
every natural input using the Chapter 4 §4.6 all-input Master-theorem bridge:
the exact-power bound `T(2^i) = Θ((i+1)·2^i)` is transferred to all inputs
through the discrete log scale `(⌊log₂ n⌋+1)·2^(⌊log₂ n⌋)`, which is then
identified with `n·log n`.
-/
theorem theta_n_log_n_all_inputs (T : ℕ → ℝ)
    (hRec : Recurrence T) (hT1 : 0 < T 1)
    (hT_mono : Chapter04.MonotoneAbs T) :
    Chapter03.isBigTheta T (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  have h_power : Chapter03.isBigTheta
      (fun i : ℕ => T (2 ^ i))
      (fun i : ℕ => Chapter04.criticalPowerLogScale 2 2 (2 ^ i)) := by
    convert theta_n_log_n_on_exact_powers T hRec hT1 using 1
    funext i
    exact (exactPower_scale_eq_criticalPowerLogScale i).symm
  have h_all : Chapter03.isBigTheta T (Chapter04.criticalPowerLogScale 2 2) :=
    Chapter04.allInput_bigTheta_of_powerStep 2 T (Chapter04.criticalPowerLogScale 2 2)
      (by norm_num : (1 : ℕ) < 2)
      hT_mono
      (Chapter04.criticalPowerLogScale_monotoneAbs 2 2 (by norm_num : (1 : ℕ) ≤ 2))
      (Chapter04.criticalPowerLogScale_powerStepBound 2 2 (by norm_num : (1 : ℕ) ≤ 2)
        (by norm_num : (1 : ℕ) < 2))
      h_power
  have h_scale : Chapter03.isBigTheta
      (Chapter04.criticalPowerLogScale 2 2) (Chapter04.realLogLogScale 2 2) :=
    Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale 2 2
      (by norm_num : (1 : ℕ) ≤ 2) (by norm_num : (1 : ℕ) < 2)
  have h_loglog : Chapter03.isBigTheta T (Chapter04.realLogLogScale 2 2) :=
    Chapter03.isBigTheta_trans h_all h_scale
  have h_eq_scale : Chapter03.isBigTheta
      (Chapter04.realLogLogScale 2 2) (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
    convert Chapter03.isBigTheta_refl (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) using 1
    funext n
    exact realLogLogScale_two_two n
  exact Chapter03.isBigTheta_trans h_loglog h_eq_scale

/-!
### Connection to existing results

The existing `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`
already proves the **exact** closed form T(2^k) = (k+1)·2^k for the
power-of-two recurrence.  The result above recovers the same asymptotic
bound (Θ(n log n)) from the general recurrence using the Master Theorem,
without computing the exact closed form.

The all-input bound `theta_n_log_n_all_inputs` now extends this from exact
powers of two to every natural input size, using the Chapter 4 §4.6
floor/ceiling sandwich bridge.
-/

end MergeSortRecurrence
end Chapter02
end CLRS
