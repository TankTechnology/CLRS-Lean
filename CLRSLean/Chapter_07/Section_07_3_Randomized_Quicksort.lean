import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import Mathlib

/-!
# CLRS Section 7.3 - Randomized quicksort

This section defines the expected-comparison recurrence for randomized quicksort
(CLRS equation (7.4)) and proves its closed-form solution, giving the
{lit}`O(n log n)` average-case bound for the first time in CLRS-Lean.

The expected number of comparisons {lit}`expectedComparisons n` = {lit}`E[T(n)]`
satisfies:
- {lit}`T(0) = 0`, {lit}`T(1) = 0`
- For {lit}`n >= 1`: {lit}`T(n) = n-1 + (2/n) * sum_{k=0}^{n-1} T(k)`

The closed form is {lit}`T(n) = 2(n+1)H_n - 4n` where {lit}`H_n` is the {lit}`n`-th
harmonic number. This yields {lit}`T(n) <= 2n H_n` and {lit}`T(n) <= n^2`
(quadratic fallback).

Main results:

- Lemma {lit}`harmonic_succ`: recurrence for harmonic numbers
- Lemma {lit}`harmonic_le_n`: {lit}`H_n <= n`
- Lemma {lit}`sum_mul_harmonic_eq`: {lit}`sum_{k=1}^{n} k H_k = n(n+1)/2 H_n - n(n-1)/4`
- Lemma {lit}`sum_expectedComparisons_eq`: closed form of {lit}`sum_{k=0}^{n-1} T(k)`
- Theorem {lit}`expectedComparisons_closed_form`: named CLRS closed-form formula
- Theorem {lit}`expectedComparisons_recurrence`: closed form satisfies CLRS (7.4)
- Theorem {lit}`expectedComparisons_telescope`: {lit}`(n+1)T(n+1) = (n+2)T(n) + 2n`
- Theorem {lit}`expectedComparisons_clrs_harmonic_bound`: {lit}`T(n) <= 2(n+1)H_n`
- Theorem {lit}`expectedComparisons_harmonic_bound`: {lit}`T(n) <= 2n H_n`
- Theorem {lit}`expectedComparisons_quadratic`: {lit}`T(n) <= n^2`
- Theorem {lit}`expectedComparisons_monotone`: {lit}`T(n) <= T(n+1)`

## Implementation details

The detailed probability proof remains available outside the main sidebar:

* [7.3 Randomized Quicksort: Comparison Probability](CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort/Comparison_Probability/)

Notation conventions:

- {lit}`harmonic n` : {lit}`H_n`, the {lit}`n`-th harmonic number in {lit}`Q`
- {lit}`expectedComparisons n` : {lit}`T(n)`, expected number of comparisons
  for randomized quicksort on {lit}`n` distinct elements
-/

namespace CLRS
namespace Chapter07

open Chapter07

/-! ## Harmonic numbers -/

/--
The {lit}`n`-th harmonic number as a rational. {lit}`H_0 = 0`,
{lit}`H_{n+1} = H_n + 1/(n+1)`.
-/
def harmonic : Nat → Rat
  | 0 => 0
  | n+1 => harmonic n + 1 / ((n+1 : Nat) : Rat)

@[simp]
theorem harmonic_zero : harmonic 0 = 0 := rfl

@[simp]
theorem harmonic_one : harmonic 1 = 1 := by
  simp [harmonic]

/-- Recurrence for harmonic numbers: {lit}`H_{n+1} = H_n + 1/(n+1)`. -/
theorem harmonic_succ (n : Nat) : harmonic (n+1) = harmonic n + (1 : Rat) / ((n+1 : Nat) : Rat) :=
  rfl

/-- Harmonic numbers are nonnegative. -/
theorem harmonic_nonneg (n : Nat) : 0 ≤ harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [harmonic_succ]
      have hpos : 0 ≤ (1 : Rat) / ((n+1 : Nat) : Rat) := by
        positivity
      nlinarith

/--
The harmonic number is bounded by its index: {lit}`H_n <= n` for all {lit}`n`.

This trivial bound is enough for many estimates.
-/
theorem harmonic_le_n (n : Nat) : harmonic n ≤ (n : Rat) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [harmonic_succ]
      push_cast
      have hdiv : (1 : Rat) / ((n : Rat) + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by nlinarith)
      nlinarith

/-! ## Expected comparisons: closed form -/

/--
Expected number of comparisons in randomized quicksort on {lit}`n` distinct
elements, given by the closed-form solution of CLRS recurrence (7.4):

{lit}`T(n) = 2(n+1)H_n - 4n`

where {lit}`H_n` is the {lit}`n`-th harmonic number. This is a computable
deterministic rational function; the expectation is folded into the recurrence
coefficients, not into a probability space.
-/
def expectedComparisons (n : Nat) : Rat :=
  2 * ((n : Rat) + 1) * harmonic n - 4 * (n : Rat)

/-- Named CLRS closed form for randomized-quicksort expected comparisons. -/
theorem expectedComparisons_closed_form (n : Nat) :
    expectedComparisons n = 2 * ((n : Rat) + 1) * harmonic n - 4 * (n : Rat) :=
  rfl

@[simp]
theorem expectedComparisons_zero : expectedComparisons 0 = 0 := by
  simp [expectedComparisons, harmonic]

@[simp]
theorem expectedComparisons_one : expectedComparisons 1 = 0 := by
  simp [expectedComparisons, harmonic]
  ring

/-- Explicit formula for {lit}`expectedComparisons (n+1)` in terms of {lit}`harmonic (n+1)`. -/
theorem expectedComparisons_succ (n : Nat) :
    expectedComparisons (n+1) = 2 * ((n+1 : Rat) + 1) * harmonic (n+1) - 4 * ((n+1 : Rat)) := by
  simp [expectedComparisons]

/-! ## Key combinatorial identity - sum of k times harmonic k -/

/--
Central combinatorial identity for the expected-quicksort closed form:

{lit}`sum_{k=1}^{n} k * H_k = (n(n+1)/2) * H_n - n(n-1)/4`

This is proved by induction on {lit}`n` using the harmonic recurrence to
express {lit}`H_n` in terms of {lit}`H_{n+1}` in the inductive step.
-/
theorem sum_mul_harmonic_eq (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n, ((k : Rat) * harmonic k)) =
    (((n : Rat) * ((n : Rat) + 1)) / 2) * harmonic n - ((n : Rat) * ((n : Rat) - 1) / 4) := by
  induction n with
  | zero =>
      simp [harmonic]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega) (fun k => (k : Rat) * harmonic k)]
      rw [ih]
      -- Now: (n(n+1)/2)*H_n - n(n-1)/4 + (n+1)*H_{n+1} = ((n+1)(n+2)/2)*H_{n+1} - (n+1)n/4
      -- Use H_n = H_{n+1} - 1/(n+1)
      have hH_n : harmonic n = harmonic (n+1) - (1 : Rat) / ((n+1 : Nat) : Rat) := by
        rw [harmonic_succ]
        ring
      rw [hH_n]
      push_cast
      ring_nf
      have hpos : ((n : Nat) : Rat) + 1 ≠ 0 := by
        intro hzero
        have hsum : ((n+1 : Nat) : Rat) = 0 := by push_cast; simpa using hzero
        exact Nat.succ_ne_zero n (by exact_mod_cast hsum)
      field_simp [hpos]
      ring

/-! ## Sum of expected comparisons -/

/--
Closed form for the sum of expected comparisons up to {lit}`n-1`:

{lit}`sum_{k=0}^{n-1} T(k) = n(n+1)*H_n - (5 n^2 - n)/2`
-/
theorem sum_expectedComparisons_eq (n : Nat) :
    (∑ k ∈ Finset.range n, expectedComparisons k) =
    ((n : Rat) * ((n : Rat) + 1)) * harmonic n - ((5 : Rat) * (n : Rat) * (n : Rat) - (n : Rat)) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, expectedComparisons, ih]
      have hH_succ : harmonic (n+1) = harmonic n + (1 : Rat) / ((n+1 : Nat) : Rat) := harmonic_succ n
      rw [hH_succ]
      push_cast
      ring_nf
      have hpos : ((n : Nat) : Rat) + 1 ≠ 0 := by
        intro hzero
        have hsum : ((n+1 : Nat) : Rat) = 0 := by push_cast; simpa using hzero
        exact Nat.succ_ne_zero n (by exact_mod_cast hsum)
      field_simp [hpos]
      ring

/-! ## Recurrence verification -/

/--
The closed-form {lit}`expectedComparisons` satisfies the CLRS expected-comparison
recurrence (7.4): for {lit}`n >= 1`,

{lit}`T(n) = n-1 + (2/n) * sum_{k=0}^{n-1} T(k)`.

The proof multiplies through by {lit}`n` and uses the closed form of the sum.
-/
theorem expectedComparisons_recurrence (n : Nat) (hn : n ≥ 1) :
    expectedComparisons n = ((n : Rat) - 1) + (2 / (n : Rat)) *
      (∑ k ∈ Finset.range n, expectedComparisons k) := by
  have hnpos : (n : Rat) ≠ 0 := by
    intro hzero
    have : n = 0 := by exact_mod_cast hzero
    omega
  -- Clear denominator by multiplying both sides by n
  field_simp [hnpos]
  -- Goal: n * T(n) = n * (n-1) + 2 * S(n)
  rw [sum_expectedComparisons_eq n]
  rw [expectedComparisons]
  ring

/--
Alternative form of the recurrence, clearing denominators:

{lit}`(n+1) * T(n+1) = (n+2) * T(n) + 2n`  for all {lit}`n >= 0`.

This telescoping identity is the key to the closed form and is used in the
inductive proofs below.
-/
theorem expectedComparisons_telescope (n : Nat) :
    ((n+1 : Nat) : Rat) * expectedComparisons (n+1) =
    (((n : Rat) + 2)) * expectedComparisons n + 2 * (n : Rat) := by
  rw [expectedComparisons, expectedComparisons]
  have hH_succ : harmonic (n+1) = harmonic n + (1 : Rat) / ((n+1 : Nat) : Rat) := harmonic_succ n
  rw [hH_succ]
  push_cast
  ring_nf
  have hpos : ((n : Nat) : Rat) + 1 ≠ 0 := by
    intro hzero
    have hsum : ((n+1 : Nat) : Rat) = 0 := by push_cast; simpa using hzero
    exact Nat.succ_ne_zero n (by exact_mod_cast hsum)
  field_simp [hpos]
  ring

/-! ## Expected comparisons: nonnegativity -/

/-- Expected comparisons are nonnegative. -/
theorem expectedComparisons_nonneg (n : Nat) : 0 ≤ expectedComparisons n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ht := expectedComparisons_telescope n
      -- ht: (n+1)*T(n+1) = (n+2)*T(n) + 2n
      -- RHS >= 0 since T(n) >= 0 and n >= 0, and (n+1) > 0 so T(n+1) >= 0
      have hpos_denom : ((n+1 : Nat) : Rat) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have hnum_nonneg : 0 ≤ (((n : Rat) + 2)) * expectedComparisons n + 2 * (n : Rat) := by
        nlinarith
      -- From ht: T(n+1) = numerator / (n+1)
      have hT_expr : expectedComparisons (n+1) =
          ((((n : Rat) + 2)) * expectedComparisons n + 2 * (n : Rat)) / ((n+1 : Nat) : Rat) :=
        (eq_div_iff_mul_eq hpos_denom).mpr (by
          -- Need: T(n+1) * (n+1) = numerator
          -- ht gives: (n+1) * T(n+1) = numerator
          simpa [mul_comm] using ht)
      rw [hT_expr]
      refine div_nonneg hnum_nonneg (by positivity)

/-! ## Bounds -/

/--
**Harmonic upper bound.** The expected number of comparisons in randomized
quicksort is at most {lit}`2 n * H_n`.

Since {lit}`H_n = Theta(log n)`, this gives {lit}`T(n) = O(n log n)`.
-/
theorem expectedComparisons_harmonic_bound (n : Nat) :
    expectedComparisons n ≤ 2 * (n : Rat) * harmonic n := by
  have hle : harmonic n ≤ (n : Rat) := harmonic_le_n n
  rw [expectedComparisons]
  nlinarith

/--
CLRS-facing harmonic upper bound using the closed-form scale
{lit}`2(n+1)H_n`.
-/
theorem expectedComparisons_clrs_harmonic_bound (n : Nat) :
    expectedComparisons n ≤ 2 * ((n : Rat) + 1) * harmonic n := by
  rw [expectedComparisons_closed_form]
  have hn : 0 ≤ (4 : Rat) * (n : Rat) := by positivity
  nlinarith

/--
**Quadratic upper bound.** On any input of length {lit}`n`, the expected number
of comparisons is at most {lit}`n^2`.

The proof uses induction with the telescope identity:
{lit}`T(n+1) = ((n+2)T(n) + 2n)/(n+1)`.  The inductive hypothesis
{lit}`T(n) <= n^2` and a simple polynomial inequality {lit}`n^2 + n + 1 >= 0`
close the step.
-/
theorem expectedComparisons_quadratic (n : Nat) :
    expectedComparisons n ≤ (n : Rat) * (n : Rat) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ht := expectedComparisons_telescope n
      -- ht: (n+1)*T(n+1) = (n+2)*T(n) + 2n
      have hpos : ((n+1 : Nat) : Rat) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      -- From ht: T(n+1) = ((n+2)*T(n) + 2n) / (n+1)
      have hT_succ : expectedComparisons (n+1) =
          ((((n : Rat) + 2)) * expectedComparisons n + 2 * (n : Rat)) / ((n+1 : Nat) : Rat) :=
        (eq_div_iff_mul_eq hpos).mpr (by
          simpa [mul_comm] using ht)
      rw [hT_succ]
      -- Need: ((n+2)*T(n) + 2n) / (n+1) <= (n+1)^2
      -- First, bound the numerator using ih: T(n) <= n^2
      have hnum_bound : (((n : Rat) + 2)) * expectedComparisons n + 2 * (n : Rat) ≤
          ((n : Rat) + 1) * ((n : Rat) + 1) * ((n : Rat) + 1) := by
        -- (n+2)*T(n) + 2n <= (n+2)*n^2 + 2n = n^3 + 2n^2 + 2n
        -- <= n^3 + 3n^2 + 3n + 1 = (n+1)^3  (since n^2 + n + 1 >= 0)
        nlinarith
      -- Apply the division lemma: if a <= b and c > 0, then a/c <= b/c
      refine le_trans (div_le_div_of_nonneg_right hnum_bound (by positivity)) ?_
      -- Now need: (n+1)^3 / (n+1) <= (n+1)^2
      -- Since (n+1)^3 / (n+1) = (n+1)^2 exactly, this is equality
      push_cast
      have h_eq : ((n : Rat) + 1) * ((n : Rat) + 1) * ((n : Rat) + 1) / ((n : Rat) + 1) =
          ((n : Rat) + 1) * ((n : Rat) + 1) := by
        field_simp [show ((n : Rat) + 1) ≠ 0 from by positivity]
      exact h_eq.le

/--
**Monotonicity.** The expected comparison count is non-decreasing:
{lit}`T(n) <= T(n+1)`.

From the telescope identity, {lit}`T(n+1) - T(n) = (T(n) + 2n)/(n+1) >= 0`.
-/
theorem expectedComparisons_monotone (n : Nat) : expectedComparisons n ≤ expectedComparisons (n+1) := by
  have ht := expectedComparisons_telescope n
  -- ht: (n+1)*T(n+1) = (n+2)*T(n) + 2n
  -- Rearranged: (n+1)*(T(n+1) - T(n)) = T(n) + 2n
  -- Since T(n) >= 0, RHS >= 0, so T(n+1) - T(n) >= 0
  have hpos : ((n+1 : Nat) : Rat) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hnonneg : 0 ≤ expectedComparisons n := expectedComparisons_nonneg n
  have hdiff : expectedComparisons (n+1) - expectedComparisons n =
      (expectedComparisons n + 2 * (n : Rat)) / ((n+1 : Nat) : Rat) :=
    (eq_div_iff_mul_eq hpos).mpr (by
      -- Need: (T(n+1) - T(n)) * (n+1) = T(n) + 2n
      -- Start from ht: (n+1)*T(n+1) = (n+2)*T(n) + 2n
      calc
        (expectedComparisons (n+1) - expectedComparisons n) * ((n+1 : Nat) : Rat)
            = ((n+1 : Nat) : Rat) * expectedComparisons (n+1) -
              ((n+1 : Nat) : Rat) * expectedComparisons n := by ring
        _ = (((n : Rat) + 2) * expectedComparisons n + 2 * (n : Rat)) -
              ((n+1 : Nat) : Rat) * expectedComparisons n := by rw [ht]
        _ = expectedComparisons n + 2 * (n : Rat) := by push_cast; ring
      )
  have hdiff_nonneg : 0 ≤ expectedComparisons (n+1) - expectedComparisons n := by
    rw [hdiff]
    refine div_nonneg ?_ (by positivity)
    nlinarith
  linarith

end Chapter07
end CLRS
