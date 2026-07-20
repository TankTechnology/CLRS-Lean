import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import CLRSLean.Probability.FiniteExpectation
import Mathlib
import Mathlib.NumberTheory.Harmonic.Bounds

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

/-! ## Asymptotic Θ(n log n) bound

We now lift the harmonic upper bound to the textbook asymptotic statement
{lit}`T(n) = Θ(n log n)` using the standard harmonic bounds
{lit}`log(n+1) ≤ H_n ≤ 1 + log n` from Mathlib.
-/

open Chapter03

/--
The rational harmonic number defined in this section equals Mathlib's global
harmonic number after casting to {lit}`ℝ`.
-/
theorem harmonic_eq_mathlib_harmonic (n : ℕ) : (harmonic n : ℝ) = (_root_.harmonic n : ℝ) := by
  induction n with
  | zero => simp [harmonic, _root_.harmonic]
  | succ n ih =>
    rw [harmonic_succ, _root_.harmonic_succ]
    push_cast
    rw [ih]
    simp

/--
Expected comparisons cast to {lit}`ℝ`, for use with the Chapter 3 asymptotic
wrappers.
-/
noncomputable def expectedComparisonsReal (n : ℕ) : ℝ := (expectedComparisons n : ℝ)

/-- Cast of the harmonic upper bound to {lit}`ℝ`. -/
theorem expectedComparisons_harmonic_bound_real (n : ℕ) :
    expectedComparisonsReal n ≤ 2 * (n : ℝ) * (harmonic n : ℝ) := by
  have h := expectedComparisons_harmonic_bound n
  dsimp [expectedComparisonsReal]
  exact_mod_cast h

/--
**Lower bound.**  For {lit}`n ≥ 1`, the expected number of comparisons is at
least {lit}`n * H_n - 4n`.
-/
theorem expectedComparisons_lower_bound_real (n : ℕ) (_hn : 1 ≤ n) :
    (n : ℝ) * (harmonic n : ℝ) - 4 * (n : ℝ) ≤ expectedComparisonsReal n := by
  dsimp [expectedComparisonsReal, expectedComparisons]
  push_cast
  have h_nonneg : 0 ≤ (harmonic n : ℝ) := by exact mod_cast harmonic_nonneg n
  nlinarith

/-- The local harmonic after casting is bounded by {lit}`1 + log n`. -/
theorem harmonic_le_one_add_log' (n : ℕ) : (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  rw [harmonic_eq_mathlib_harmonic n]
  exact harmonic_le_one_add_log n

/-- The local harmonic after casting is bounded below by {lit}`log (n+1)`. -/
theorem log_add_one_le_harmonic' (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) := by
  rw [harmonic_eq_mathlib_harmonic n]
  simpa [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n

/--
**Randomized quicksort is {lit}`O(n log n)`.**  The expected number of
comparisons satisfies {lit}`T(n) = O(n log n)`.
-/
theorem expectedComparisons_isBigO_nlogn :
    isBigO expectedComparisonsReal (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  rw [isBigO_iff]
  have h_harm_le : ∀ n : ℕ, (harmonic n : ℝ) ≤ 1 + Real.log (n : ℝ) := harmonic_le_one_add_log'
  -- Real.log → ∞, so eventually log n ≥ 1
  have h_log_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (Filter.eventually_ge_atTop (1 : ℝ))
  rcases Filter.eventually_atTop.mp h_log_eventually with ⟨n₁, hn₁⟩
  refine ⟨4, by norm_num, max 2 n₁, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn_log_ge_one : (1 : ℝ) ≤ Real.log (n : ℝ) := hn₁ n (le_trans (le_max_right _ _) hn)
  have hn_pos : 1 ≤ n := by omega
  have hn_real_pos : 1 ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_real_pos
  have hT_nonneg : 0 ≤ expectedComparisonsReal n := by
    dsimp [expectedComparisonsReal]; exact mod_cast expectedComparisons_nonneg n
  have hmul_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
  rw [abs_of_nonneg hT_nonneg, abs_of_nonneg hmul_nonneg]
  calc
    expectedComparisonsReal n ≤ 2 * (n : ℝ) * (harmonic n : ℝ) := expectedComparisons_harmonic_bound_real n
    _ ≤ 2 * (n : ℝ) * (1 + Real.log (n : ℝ)) := by
      have h_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
      gcongr
      exact h_harm_le n
    _ = 2 * (n : ℝ) + 2 * ((n : ℝ) * Real.log (n : ℝ)) := by ring
    _ ≤ 4 * ((n : ℝ) * Real.log (n : ℝ)) := by
      -- 2n ≤ 2n*log n  when log n ≥ 1, so 2n + 2n*log n ≤ 4n*log n
      have h : 2 * (n : ℝ) ≤ 2 * ((n : ℝ) * Real.log (n : ℝ)) := by
        have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        calc
          2 * (n : ℝ) = 2 * (n : ℝ) * (1 : ℝ) := by ring
          _ ≤ 2 * (n : ℝ) * Real.log (n : ℝ) := by gcongr
          _ = 2 * ((n : ℝ) * Real.log (n : ℝ)) := by ring
      nlinarith

/--
**Randomized quicksort is {lit}`Ω(n log n)`.**  The expected number of
comparisons satisfies {lit}`T(n) = Ω(n log n)`.
-/
theorem expectedComparisons_isBigOmega_nlogn :
    isBigOmega expectedComparisonsReal (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  rw [isBigOmega_iff]
  -- Use log(n+1) ≤ H_n and T(n) ≥ n*H_n - 4n
  have h_harm_lower : ∀ n : ℕ, Real.log ((n : ℝ) + 1) ≤ (harmonic n : ℝ) :=
    log_add_one_le_harmonic'
  -- Real.log → ∞, so eventually log n ≥ 8
  have h_log_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, (8 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (Filter.eventually_ge_atTop (8 : ℝ))
  rcases Filter.eventually_atTop.mp h_log_eventually with ⟨n₀₁, hn₀₁⟩
  -- Also need log(n+1) ≥ (1/2)*log n for large n
  -- Since log(n+1)/log n → 1, for log n ≥ 8 we have log(n+1) ≥ (3/4)*log n
  -- Actually log(n+1) ≥ log n ≥ (1/2)*log n trivially
  let n₀ := max n₀₁ 8
  refine ⟨1/8, by norm_num, n₀, fun n hn => ?_⟩
  have hn₁ : n₀₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : 8 ≤ n := le_trans (le_max_right _ _) hn
  have hn_real_pos : 0 < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hT_nonneg : 0 ≤ expectedComparisonsReal n := by
    dsimp [expectedComparisonsReal]; exact mod_cast expectedComparisons_nonneg n
  have hn1pos : 1 ≤ n := by omega
  have hn1real : 1 ≤ (n : ℝ) := by exact_mod_cast hn1pos
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1real
  have hmul_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by positivity
  rw [abs_of_nonneg hT_nonneg, abs_of_nonneg hmul_nonneg]
  have h_log_ge_eight : (8 : ℝ) ≤ Real.log (n : ℝ) := hn₀₁ n hn₁
  -- log(n+1) ≥ log n ≥ 8 for n ≥ n₀
  have h_log_succ_ge : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by nlinarith)
  -- T(n) ≥ n*H_n - 4n ≥ n*log(n+1) - 4n ≥ n*log n - 4n
  -- Since log n ≥ 8, we have log n/8 ≥ 1, so 4n ≤ (log n/2)*n = n*log n/2
  -- Thus n*log n - 4n ≥ n*log n/2 ≥ n*log n/8
  calc
    (1/8 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) = ((n : ℝ) * Real.log (n : ℝ)) / 8 := by ring
    _ ≤ ((n : ℝ) * Real.log (n : ℝ)) - 4 * (n : ℝ) := by
      -- Need: (n*log n)/8 ≤ n*log n - 4n  ⇔  4n ≤ (7/8)*n*log n  ⇔  32/7 ≤ log n ≈ 4.57
      -- Since log n ≥ 8, this holds.
      have h : 4 * (n : ℝ) ≤ (7/8 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by
        calc
          4 * (n : ℝ) = (n : ℝ) * 4 := by ring
          _ ≤ (n : ℝ) * ((7/8 : ℝ) * Real.log (n : ℝ)) := by
            nlinarith [h_log_ge_eight]
          _ = (7/8 : ℝ) * ((n : ℝ) * Real.log (n : ℝ)) := by ring
      nlinarith
    _ ≤ (n : ℝ) * Real.log ((n : ℝ) + 1) - 4 * (n : ℝ) := by nlinarith
    _ ≤ (n : ℝ) * (harmonic n : ℝ) - 4 * (n : ℝ) := by nlinarith [h_harm_lower n]
    _ ≤ expectedComparisonsReal n := expectedComparisons_lower_bound_real n hn1pos

/--
**Randomized quicksort is {lit}`Θ(n log n)`.**  The expected number of
comparisons satisfies {lit}`T(n) = Θ(n log n)`.
-/
theorem expectedComparisons_isBigTheta_nlogn :
    isBigTheta expectedComparisonsReal (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) :=
  ⟨expectedComparisons_isBigO_nlogn, expectedComparisons_isBigOmega_nlogn⟩

/-! ## Bridge: probability model to closed form

We connect the random-permutation pairwise comparison probability
(`compared_prob`, CLRS Theorem 7.3) to the deterministic closed form
`expectedComparisons n` and the `Θ(n log n)` asymptotic.
-/

open CLRS.Probability

/-- Additive recurrence: `T(n+1) = T(n) + 2*(H_{n+1} - 1)`. -/
theorem expectedComparisons_succ_add_two (n : ℕ) :
    expectedComparisons (n+1) = expectedComparisons n + 2 * (harmonic (n+1) - 1) := by
  have ht := expectedComparisons_telescope n
  have hpos : ((n+1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hT_succ : expectedComparisons (n+1) =
      (((n : ℚ) + 2) * expectedComparisons n + 2 * (n : ℚ)) / ((n+1 : ℕ) : ℚ) :=
    (eq_div_iff_mul_eq hpos).mpr (by simpa [mul_comm] using ht)
  rw [hT_succ]
  rw [show expectedComparisons n = 2 * ((n : ℚ) + 1) * harmonic n - 4 * (n : ℚ) from rfl]
  have hH_succ : harmonic (n+1) = harmonic n + (1 : ℚ) / ((n+1 : ℕ) : ℚ) := harmonic_succ n
  rw [hH_succ]
  push_cast
  field_simp [show ((n : ℚ) + 1) ≠ 0 from by positivity]
  ring

/-- The double sum of pairwise comparison probabilities `2/(j-i+1)`
over all `0 ≤ i < j < n` equals the expected-comparison closed form. -/
theorem sum_compared_prob_eq_expectedComparisons (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0) =
    (expectedComparisons n : ℚ) := by
  induction n with
  | zero => simp [expectedComparisons]
  | succ n ih =>
    -- S(n+1) = S(n) + A(n), where A(n) = Σ_{i<n} 2/(n-i+1)
    -- Split the outer sum: i=n contributes nothing (n < j never holds in range (n+1))
    rw [Finset.sum_range_succ]
    have h_last_row_zero : (∑ j ∈ Finset.range (n+1),
        if (n : ℕ) < j then (2 : ℚ) / ((j - n + 1 : ℕ) : ℚ) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      rw [Finset.mem_range] at hj
      simp [show ¬ (n : ℕ) < j from by omega]
    rw [h_last_row_zero, add_zero]
    -- For i < n, split inner sum at j = n (the new column)
    have h_inner_split : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n+1),
        if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0) =
        (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0) +
        (∑ i ∈ Finset.range n, (2 : ℚ) / (((n : ℕ) - i + 1 : ℕ) : ℚ)) := by
      calc
        (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n+1),
          if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0)
            = (∑ i ∈ Finset.range n,
                ((∑ j ∈ Finset.range n, if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0) +
                  (if i < n then (2 : ℚ) / (((n : ℕ) - i + 1 : ℕ) : ℚ) else 0))) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
              if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0) +
            (∑ i ∈ Finset.range n,
              (if i < n then (2 : ℚ) / (((n : ℕ) - i + 1 : ℕ) : ℚ) else 0)) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
              if i < j then (2 : ℚ) / ((j - i + 1 : ℕ) : ℚ) else 0) +
            (∑ i ∈ Finset.range n, (2 : ℚ) / (((n : ℕ) - i + 1 : ℕ) : ℚ)) := by
          congr 1
          apply Finset.sum_congr rfl; intro i hi
          have hi_lt_n : i < n := Finset.mem_range.1 hi
          simp [hi_lt_n]
    rw [h_inner_split, ih]
    rw [expectedComparisons_succ_add_two n]
    congr 1
    -- Prove A(n) = 2*(H_{n+1} - 1) using the same recurrence
    -- A(0) = 0, A(n+1) = A(n) + 2/(n+2)
    -- Both sides satisfy this recurrence
    have hA_recurrence : ∀ m, (∑ i ∈ Finset.range m, (2 : ℚ) / (((m : ℕ) - i + 1 : ℕ) : ℚ)) =
        2 * (harmonic (m+1) - 1) := by
      intro m
      induction m with
      | zero => simp [harmonic]
      | succ m ih =>
        -- A(m+1) = Σ_{i∈range(m+1)} 2/((m+1)-i+1)
        -- Decompose: i=0 term = 2/(m+2), remaining shifted by i↦i+1
        have h_decomp : (Finset.range (m+1) : Finset ℕ) =
            ({0} : Finset ℕ) ∪ ((Finset.range m).map ⟨(· + 1), Nat.succ_injective⟩) := by
          ext i; constructor
          · intro hi
            have hi_val : i < m+1 := Finset.mem_range.1 hi
            rcases Nat.eq_zero_or_pos i with (rfl | hpos)
            · apply Finset.mem_union_left; simp
            · apply Finset.mem_union_right
              apply Finset.mem_map.mpr
              have h_bound : i - 1 < m := by omega
              refine ⟨i-1, Finset.mem_range.2 h_bound, ?_⟩
              have h_one_le : 1 ≤ i := Nat.one_le_of_lt hpos
              dsimp
              rw [Nat.sub_add_cancel h_one_le]
          · intro hi
            rcases Finset.mem_union.1 hi with (h | h)
            · rcases Finset.mem_singleton.1 h with rfl
              exact Finset.mem_range.2 (by
                have : 0 < m+1 := Nat.zero_lt_succ m
                exact this)
            · rcases Finset.mem_map.1 h with ⟨j, hj, rfl⟩
              have hj_val : j < m := Finset.mem_range.1 hj
              have : j+1 < m+1 := Nat.add_lt_add_right hj_val 1
              exact Finset.mem_range.2 this
        have h_disjoint : Disjoint ({0} : Finset ℕ) ((Finset.range m).map ⟨(· + 1), Nat.succ_injective⟩) := by
          refine Finset.disjoint_singleton_left.mpr (fun h => ?_)
          rcases Finset.mem_map.1 h with ⟨j, hj, h⟩
          have : j + 1 = 0 := h
          omega
        rw [h_decomp, Finset.sum_union h_disjoint,
          Finset.sum_singleton, Finset.sum_map]
        -- Now: 2/((m+1)-0+1) + Σ_{j∈range m} 2/((m+1)-(j+1)+1)
        -- = 2/(m+2) + Σ_{j∈range m} 2/(m-j+1)
        -- = 2/(m+2) + A(m)
        simp only [Function.Embedding.coeFn_mk]
        have h0 : ((m+1 : ℕ) - 0 + 1 : ℕ) = (m+2 : ℕ) := by omega
        have h_shift : ∀ j, ((m+1 : ℕ) - (j+1) + 1 : ℕ) = ((m : ℕ) - j + 1 : ℕ) := by
          intro j; omega
        simp_rw [h0, h_shift]
        rw [ih]
        rw [harmonic_succ (m+1)]
        push_cast; ring
    exact hA_recurrence n

end Chapter07
end CLRS
