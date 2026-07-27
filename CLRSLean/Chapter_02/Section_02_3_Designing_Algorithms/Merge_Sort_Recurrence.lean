import Mathlib
import CLRSLean.Chapter_02.Section_02_3_Designing_Algorithms
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# CLRS §2.3 — Merge Sort Recurrence and Θ(n log n) Bound

This file formalizes the merge sort recurrence from CLRS §2.3:

> T(n) = T(⌊n/2⌋) + T(⌈n/2⌉) + Θ(n)

and proves the tight asymptotic bound T(n) = Θ(n log n).

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

/-!
### Connection to existing results

The existing `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`
already proves the **exact** closed form T(2^k) = (k+1)·2^k for the
power-of-two recurrence.  The result above recovers the same asymptotic
bound (Θ(n log n)) from the general recurrence using the Master Theorem,
without computing the exact closed form.

For the full arbitrary-input bound (with floors/ceilings), see
Chapter 4 §4.6, which extends the Master Theorem to all input sizes
via floor/ceiling sandwiching.
-/

end MergeSortRecurrence
end Chapter02
end CLRS
