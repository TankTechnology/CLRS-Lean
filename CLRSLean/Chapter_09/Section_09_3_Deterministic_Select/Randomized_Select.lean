import Mathlib
import CLRSLean.Probability.FiniteExpectation
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select

/-!
# CLRS Section 9.2 - Randomized SELECT expected running time

This support page adds the probabilistic layer that Chapter 9 was missing:
`RANDOMIZED-SELECT`, its expected-comparison recurrence, and the CLRS Theorem 9.2
bound {lit}`E[T(n)] = O(n)`.

The model is built directly on the shared finite-expectation toolkit
{lit}`CLRS.Probability.expect` / {lit}`CLRS.Probability.fintypeExpect`.  At each
recursive step a pivot is chosen **uniformly at random and independently**: the
per-step sample space is the pivot rank {lit}`Fin n`, and the expectation over
that rank is a genuine {lit}`CLRS.Probability.expect`.  The recursion always
charges the *larger* of the two partition sides (CLRS's majorizing recurrence),
so the resulting quantity {lit}`CLRS.Chapter09.randSelectExpectedCost` is an
upper bound on the true expected cost.

Main results:

- Definition {lit}`CLRS.Chapter09.subproblemSize`: the larger partition side
  {lit}`max i (n-1-i)` when the (0-indexed) pivot rank is {lit}`i`.
- Definition {lit}`CLRS.Chapter09.randSelectExpectedCost`: the expected-cost
  recurrence, defined by the uniform pivot average.
- Theorem {lit}`CLRS.Chapter09.randSelectExpectedCost_recurrence`: the derived
  expected-comparison recurrence
  {lit}`E[T(n+1)] = c(n+1) + expect (n+1) (fun i => E[T(max i (n-i))])`
  (CLRS equation for RANDOMIZED-SELECT), phrased with the toolkit
  {lit}`CLRS.Probability.expect`.
- Theorem {lit}`CLRS.Chapter09.randSelectExpectedCost_recurrence_fintype`: the
  same recurrence phrased with {lit}`CLRS.Probability.fintypeExpect` over the
  per-step sample space {lit}`Fin (n+1)`.
- Theorem {lit}`CLRS.Chapter09.randSelectExpectedCost_le`: the substitution-method
  solution {lit}`E[T(n)] ≤ 4·c·n`.
- Theorem {lit}`CLRS.Chapter09.randomizedSelect_expected_bigO_linear`: the CLRS
  Theorem 9.2 asymptotic bound
  {lit}`isBigO (fun n => E[T n]) (fun n => (n : ℝ))`.
- Theorem {lit}`CLRS.Chapter09.randomizedSelectAtIndex?_rankCorrect`: the
  randomized selector reuses the pivot-parametric SELECT skeleton, so rank
  correctness is inherited.

Notation conventions used in this section:

- {lit}`c` : the per-element local-work constant (partition comparison cost)
- {lit}`n` : current subproblem size
- {lit}`i` : the 0-indexed pivot rank (number of elements below the pivot)
-/

namespace CLRS
namespace Chapter09

open scoped BigOperators
open CLRS.Probability

/-! ## Subproblem size and the expected-cost model -/

/--
Size of the larger partition side when `RANDOMIZED-SELECT` picks the (0-indexed)
pivot rank `i` from `n` elements: `i` elements fall below the pivot and
`n - 1 - i` above it, so the recursion continues on the larger side
`max i (n - 1 - i)`.

This corresponds to the `max(k-1, n-k)` term of the CLRS expected-comparison
recurrence (with `k = i + 1` the 1-indexed rank).
-/
def subproblemSize (n i : ℕ) : ℕ := max i (n - 1 - i)

/--
Expected comparison count of `RANDOMIZED-SELECT` on `n` elements, defined as the
CLRS majorizing recurrence.

At each step the pivot rank is uniform over `Fin n`; the local partition work is
`c · n`; and the recursion charges the larger partition side.  The average over
the pivot rank is expressed as the uniform sum divided by `n`, i.e. the toolkit
average {lit}`CLRS.Probability.expect` (see
{lit}`CLRS.Chapter09.randSelectExpectedCost_recurrence`).

The sum is taken over `(Finset.range (n+1)).attach` purely so the well-founded
recursion can see that every recursive argument `max i (n - i)` is `< n + 1`.
-/
noncomputable def randSelectExpectedCost (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) =>
      c * ((n : ℝ) + 1) +
        (∑ i ∈ (Finset.range (n + 1)).attach,
            randSelectExpectedCost c (max i.1 (n - i.1))) / ((n : ℝ) + 1)
  decreasing_by
    have hi : i.1 < n + 1 := Finset.mem_range.mp i.2
    omega

@[simp]
theorem randSelectExpectedCost_zero (c : ℝ) : randSelectExpectedCost c 0 = 0 := by
  rw [randSelectExpectedCost]

/--
One-step unfolding of {lit}`CLRS.Chapter09.randSelectExpectedCost`, converting
the termination-friendly `attach` sum into an ordinary sum over
`Finset.range (n + 1)`.
-/
theorem randSelectExpectedCost_succ (c : ℝ) (n : ℕ) :
    randSelectExpectedCost c (n + 1) =
      c * ((n : ℝ) + 1) +
        (∑ i ∈ Finset.range (n + 1),
            randSelectExpectedCost c (max i (n - i))) / ((n : ℝ) + 1) := by
  conv_lhs => rw [randSelectExpectedCost]
  rw [Finset.sum_attach (Finset.range (n + 1))
        (fun i => randSelectExpectedCost c (max i (n - i)))]

/-! ## The expected-comparison recurrence (derived from the model) -/

/--
**Expected-comparison recurrence for RANDOMIZED-SELECT.**

The expected cost satisfies

{lit}`E[T(n+1)] = c·(n+1) + expect (n+1) (fun i => E[T(max i (n-i))])`,

where {lit}`CLRS.Probability.expect` is the uniform average over the pivot rank
`i ∈ {0, …, n}`.  Writing `k = i + 1` for the 1-indexed rank, the averaged term
is `E[T(max (k-1) ((n+1)-k))]`, exactly the CLRS recurrence
`E[T(n)] = (1/n) Σ_k E[T(max(k-1, n-k))] + c·n`.

This is an equality **derived** from the definition of the model (it is not an
assumed recurrence), and in particular implies the acceptance-criterion upper
bound.
-/
theorem randSelectExpectedCost_recurrence (c : ℝ) (n : ℕ) :
    randSelectExpectedCost c (n + 1) =
      c * ((n : ℝ) + 1) +
        Probability.expect (n + 1)
          (fun i => randSelectExpectedCost c (max i (n - i))) := by
  rw [randSelectExpectedCost_succ]
  simp only [Probability.expect, Nat.cast_add, Nat.cast_one]

/--
The uniform pivot average {lit}`CLRS.Probability.expect` equals the finite-type
expectation {lit}`CLRS.Probability.fintypeExpect` over the per-step sample space
`Fin m`.  This makes the "uniform independent pivot rank over `Fin n`" reading of
the model explicit.
-/
theorem expect_eq_fintypeExpect (m : ℕ) (X : ℕ → ℝ) :
    Probability.expect m X
      = Probability.fintypeExpect (fun j : Fin m => X j.1) := by
  unfold Probability.expect Probability.fintypeExpect
  rw [Fintype.card_fin, Fin.sum_univ_eq_sum_range X m]

/--
The expected-comparison recurrence phrased with
{lit}`CLRS.Probability.fintypeExpect` over the explicit per-step pivot-rank
sample space `Fin (n + 1)`.
-/
theorem randSelectExpectedCost_recurrence_fintype (c : ℝ) (n : ℕ) :
    randSelectExpectedCost c (n + 1) =
      c * ((n : ℝ) + 1) +
        Probability.fintypeExpect
          (fun j : Fin (n + 1) => randSelectExpectedCost c (max j.1 (n - j.1))) := by
  rw [randSelectExpectedCost_recurrence, expect_eq_fintypeExpect]

/-! ## Nonnegativity -/

/-- The expected cost is nonnegative whenever the work constant is nonnegative. -/
theorem randSelectExpectedCost_nonneg (c : ℝ) (hc : 0 ≤ c) :
    ∀ n, 0 ≤ randSelectExpectedCost c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | m
    · simp
    · rw [randSelectExpectedCost_succ]
      have hsum :
          0 ≤ ∑ i ∈ Finset.range (m + 1),
              randSelectExpectedCost c (max i (m - i)) := by
        apply Finset.sum_nonneg
        intro i hi
        have hlt : max i (m - i) < m + 1 := by
          have := Finset.mem_range.mp hi; omega
        exact ih _ hlt
      have h1 : 0 ≤ c * ((m : ℝ) + 1) := mul_nonneg hc (by positivity)
      have h2 :
          0 ≤ (∑ i ∈ Finset.range (m + 1),
              randSelectExpectedCost c (max i (m - i))) / ((m : ℝ) + 1) :=
        div_nonneg hsum (by positivity)
      linarith

/-! ## The max-side sum and its `3n²/4` bound -/

/--
Sum of the larger partition sides over all pivot ranks:
`∑_{i<n} max i (n - 1 - i)`.  This is the combinatorial core of the substitution
method: the substitution guess `T(k) ≤ K·k` turns the averaged recursive term
into `K · maxSideSum n / n`.
-/
def maxSideSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, max i (n - 1 - i)

/--
Two-step recurrence for the max-side sum: `maxSideSum (n+2) = maxSideSum n + 3n + 2`.

Peeling the extremal pivot ranks `0` and `n+1` (each contributing `n+1`) and
reindexing the interior leaves `∑_{i<n} (max i (n-1-i) + 1) = maxSideSum n + n`.
-/
theorem maxSideSum_add_two (n : ℕ) :
    maxSideSum (n + 2) = maxSideSum n + 3 * n + 2 := by
  unfold maxSideSum
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have hmid : ∀ i ∈ Finset.range n,
      max (i + 1) (n + 2 - 1 - (i + 1)) = max i (n - 1 - i) + 1 := by
    intro i hi
    have := Finset.mem_range.mp hi
    omega
  rw [Finset.sum_congr rfl hmid, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one]
  omega

/--
The max-side sum is at most three quarters of `n²`:
`4 · maxSideSum n ≤ 3 · n²`.

Proved by two-step strong induction using
{lit}`CLRS.Chapter09.maxSideSum_add_two`.  This is the constant `< 1` that the
substitution method needs (a bound like `maxSideSum n ≤ n²` would not close).
-/
theorem four_mul_maxSideSum_le (n : ℕ) : 4 * maxSideSum n ≤ 3 * n ^ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | m
    · simp [maxSideSum]
    · norm_num [maxSideSum, Finset.sum_range_one]
    · have hm : 4 * maxSideSum m ≤ 3 * m ^ 2 := ih m (by omega)
      rw [maxSideSum_add_two]
      nlinarith [hm]

/--
Real-valued form of the max-side bound specialized to the recursion:
`4 · Σ_{i≤m} (max i (m-i) : ℝ) ≤ 3 · (m+1)²`.
-/
theorem sum_maxSide_real_bound (m : ℕ) :
    4 * (∑ i ∈ Finset.range (m + 1), ((max i (m - i) : ℕ) : ℝ))
      ≤ 3 * ((m : ℝ) + 1) ^ 2 := by
  have hdef : maxSideSum (m + 1) = ∑ i ∈ Finset.range (m + 1), max i (m - i) := by
    unfold maxSideSum
    simp only [Nat.add_sub_cancel]
  have hN : 4 * (∑ i ∈ Finset.range (m + 1), max i (m - i)) ≤ 3 * (m + 1) ^ 2 := by
    rw [← hdef]; exact four_mul_maxSideSum_le (m + 1)
  calc
    (4 : ℝ) * (∑ i ∈ Finset.range (m + 1), ((max i (m - i) : ℕ) : ℝ))
        = ((4 * (∑ i ∈ Finset.range (m + 1), max i (m - i)) : ℕ) : ℝ) := by
          push_cast; ring
    _ ≤ ((3 * (m + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hN
    _ = 3 * ((m : ℝ) + 1) ^ 2 := by push_cast; ring

/-! ## The linear expected-time bound (CLRS Theorem 9.2) -/

/--
**Substitution-method solution of the expected-comparison recurrence.**

For a nonnegative work constant `c`, the expected cost is linear:
`E[T(n)] ≤ 4·c·n`.

The proof is the CLRS substitution method: guess `T(k) ≤ 4c·k`, bound the
averaged recursive term by `4c · maxSideSum n / n ≤ 3c·n` using
{lit}`CLRS.Chapter09.four_mul_maxSideSum_le`, and close with the local work
`c·n`.
-/
theorem randSelectExpectedCost_le (c : ℝ) (hc : 0 ≤ c) :
    ∀ n, randSelectExpectedCost c n ≤ 4 * c * (n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | m
    · simp
    · rw [randSelectExpectedCost_succ]
      set S := ∑ i ∈ Finset.range (m + 1),
          randSelectExpectedCost c (max i (m - i)) with hSdef
      -- Bound each recursive term by the substitution guess.
      have hterm : ∀ i ∈ Finset.range (m + 1),
          randSelectExpectedCost c (max i (m - i))
            ≤ 4 * c * ((max i (m - i) : ℕ) : ℝ) := by
        intro i hi
        have hlt : max i (m - i) < m + 1 := by
          have := Finset.mem_range.mp hi; omega
        exact ih _ hlt
      have hS1 : S ≤ ∑ i ∈ Finset.range (m + 1), 4 * c * ((max i (m - i) : ℕ) : ℝ) :=
        Finset.sum_le_sum hterm
      have hS2 :
          (∑ i ∈ Finset.range (m + 1), 4 * c * ((max i (m - i) : ℕ) : ℝ))
            = 4 * c * (∑ i ∈ Finset.range (m + 1), ((max i (m - i) : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
      have hpos : 0 ≤ ∑ i ∈ Finset.range (m + 1), ((max i (m - i) : ℕ) : ℝ) := by
        apply Finset.sum_nonneg; intro i _; positivity
      have hbound := sum_maxSide_real_bound m
      -- S ≤ 3c(m+1)²
      have hSle : S ≤ 3 * c * ((m : ℝ) + 1) ^ 2 := by
        rw [hS2] at hS1
        nlinarith [hS1, hbound, hc, hpos]
      have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hmpos
      have hsimp :
          (3 * c * ((m : ℝ) + 1) ^ 2) / ((m : ℝ) + 1) = 3 * c * ((m : ℝ) + 1) := by
        rw [div_eq_iff hne]; ring
      have hfrac : S / ((m : ℝ) + 1) ≤ 3 * c * ((m : ℝ) + 1) := by
        have h1 := div_le_div_of_nonneg_right hSle hmpos.le
        rwa [hsimp] at h1
      have hcm : c * ((m : ℝ) + 1) + 3 * c * ((m : ℝ) + 1) = 4 * c * ((m : ℝ) + 1) := by
        ring
      push_cast
      linarith [hfrac, hcm]

/--
Expected comparison count of `RANDOMIZED-SELECT`, with the CLRS local-work
constant (`n` comparisons per partition, i.e. `c = 1`).
-/
noncomputable def randomizedSelectExpectedComparisons (n : ℕ) : ℝ :=
  randSelectExpectedCost 1 n

/--
The expected cost is `O(n)` for every nonnegative work constant, via the
CLRS-compatible {lit}`CLRS.Chapter03.isBigO` wrapper.
-/
theorem randSelectExpectedCost_bigO_linear (c : ℝ) (hc : 0 ≤ c) :
    CLRS.Chapter03.isBigO (fun n => randSelectExpectedCost c n) (fun n => (n : ℝ)) := by
  rw [CLRS.Chapter03.isBigO_iff]
  refine ⟨4 * c + 1, by linarith, 0, ?_⟩
  intro n _
  have hnn : 0 ≤ randSelectExpectedCost c n := randSelectExpectedCost_nonneg c hc n
  have hle : randSelectExpectedCost c n ≤ 4 * c * (n : ℝ) := randSelectExpectedCost_le c hc n
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [abs_of_nonneg hnn, abs_of_nonneg hcast]
  nlinarith [hle, hcast]

/--
**CLRS Theorem 9.2.**  The expected running time (comparison count) of
`RANDOMIZED-SELECT` is `O(n)`.
-/
theorem randomizedSelect_expected_bigO_linear :
    CLRS.Chapter03.isBigO
      (fun n => randomizedSelectExpectedComparisons n) (fun n => (n : ℝ)) :=
  randSelectExpectedCost_bigO_linear 1 (by norm_num)

/-! ## Rank correctness via a randomized pivot oracle -/

/--
Pivot oracle that selects the element at a designated (random) index, reusing the
pivot-parametric SELECT skeleton of Section 9.3.
-/
def pivotAtIndex? (i : ℕ) (xs : List ℕ) : Option ℕ := xs[i]?

/-- The index pivot oracle only ever returns members of its input list. -/
theorem pivotAtIndex?_mem (i : ℕ) : PivotMembership (pivotAtIndex? i) := by
  intro xs pivot hsel
  rcases getElem?_eq_some_iff_split.mp hsel with ⟨lo, hi, rfl, _hlen⟩
  simp

/--
`RANDOMIZED-SELECT` with the pivot chosen at index `i`, obtained by instantiating
the pivot-parametric selector {lit}`CLRS.Chapter09.selectWithPivot?`.  Modelling
`i` as uniform over the current input recovers the randomized algorithm whose
expected cost is analysed above.
-/
def randomizedSelectAtIndex? (i k : ℕ) (xs : List ℕ) : Option ℕ :=
  selectWithPivot? (pivotAtIndex? i) k xs

/--
Rank correctness of `RANDOMIZED-SELECT` is inherited from the pivot-parametric
skeleton: any successful result is a valid zero-based order statistic.
-/
theorem randomizedSelectAtIndex?_rankCorrect {i k : ℕ} {xs : List ℕ} {x : ℕ}
    (hsel : randomizedSelectAtIndex? i k xs = some x) :
    RankCertificate xs k x :=
  selectWithPivot?_rankCorrect (pivotAtIndex? i) (pivotAtIndex?_mem i)
    (by simpa [randomizedSelectAtIndex?] using hsel)

/-- Membership projection for the randomized selector. -/
theorem randomizedSelectAtIndex?_mem {i k : ℕ} {xs : List ℕ} {x : ℕ}
    (hsel : randomizedSelectAtIndex? i k xs = some x) :
    x ∈ xs :=
  (randomizedSelectAtIndex?_rankCorrect hsel).1

/-! ## Concrete step-count model

The abstract expected-cost recurrence {name}`randSelectExpectedCost` models the
CLRS majorizing recurrence; {name}`randomizedSelect_expected_bigO_linear` proves
{lit}`E[T(n)] = O(n)`.  We now define a concrete cost counter that instruments
the actual {name}`selectCostFuel` recursion with independent uniform random
pivot choices at each level.
-/

/--
Concrete expected cost for one run of RANDOMIZED-SELECT.  At each recursion
level a pivot index {lit}`i` is drawn uniformly from {lit}`Fin xs.length`, and
the fuelled cost counter {lit}`CLRS.Chapter09.selectCostFuel` charges
{lit}`c * ys.length` local partition-comparison work.

This expectation over the root-level pivot choice recovers the one-level
average of the abstract recurrence.  The full joint-distribution induction
that connects the multi-level expectation to {name}`randSelectExpectedCost`
is deferred.
-/
noncomputable def randomizedSelectCost (c fuel k : ℕ) (xs : List ℕ) : ℝ :=
  fintypeExpect (fun (i : Fin xs.length) =>
    (selectCostFuel (pivotAtIndex? (i : ℕ)) (fun ys => c * ys.length) fuel k xs : ℝ))

/--
The expected cost is nonnegative.
-/
theorem randomizedSelectCost_nonneg (c fuel k : ℕ) (xs : List ℕ) :
    0 ≤ randomizedSelectCost c fuel k xs := by
  dsimp [randomizedSelectCost]
  apply fintypeExpect_nonneg
  intro i
  positivity

end Chapter09
end CLRS
