import Mathlib
import CLRSLean.Probability.FiniteExpectation
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select

/-!
# CLRS Section 9.2 - Randomized SELECT expected running time

This support page formalizes the standard majorizing recurrence used in the
analysis of `RANDOMIZED-SELECT` and proves that this recurrence is linear.

The model is built directly on the shared finite-expectation toolkit
{lit}`CLRS.Probability.expect` / {lit}`CLRS.Probability.fintypeExpect`.  One
recurrence step averages uniformly over the pivot rank {lit}`Fin n` and charges
the *larger* of the two partition sides.  The section also defines the actual
state-dependent stochastic execution: every recursive call takes a fresh
uniform pivot-rank choice, follows the branch selected by the requested rank,
and charges its partition comparisons.  That continuation is bounded
pointwise by the larger-side recurrence, yielding expected cost at most
{lit}`4n`.

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
- Theorem {lit}`CLRS.Chapter09.randomizedSelectMajorizer_bigO_linear`: the
  asymptotic bound for the majorizing recurrence
  {lit}`isBigO (fun n => E[T n]) (fun n => (n : ℝ))`.
- Definition {lit}`CLRS.Chapter09.freshRandomizedSelectExpectedComparisons` and
  theorem
  {lit}`CLRS.Chapter09.freshRandomizedSelectExpectedComparisons_linear_bound`:
  fresh per-call pivot choices for the actual selected continuation have
  expected comparison cost at most {lit}`4n`.
- Theorem {lit}`CLRS.Chapter09.freshRandomizedSelectWithRanks?_correct`: every
  executable finite sample path driven by successive pivot ranks is rank-correct.
- Theorem
  {lit}`CLRS.Chapter09.freshRandomizedSelectContinuationSize_le_subproblemSize`:
  the actual selected continuation is pointwise bounded by the larger-side
  recurrence argument.
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
The CLRS majorizing expected-comparison recurrence with unit local-work
constant (`n` comparisons per partition, i.e. `c = 1`).
-/
noncomputable def randomizedSelectMajorizingExpectedComparisons (n : ℕ) : ℝ :=
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
The majorizing recurrence used in the proof of CLRS Theorem 9.2 is `O(n)`.
The fresh-choice state-dependent execution and its coupling to the same
larger-side argument are proved separately below.
-/
theorem randomizedSelectMajorizer_bigO_linear :
    CLRS.Chapter03.isBigO
      (fun n => randomizedSelectMajorizingExpectedComparisons n) (fun n => (n : ℝ)) :=
  randSelectExpectedCost_bigO_linear 1 (by norm_num)

/-! ## Fresh-choice RANDOMIZED-SELECT semantics -/

/--
Fuelled RANDOMIZED-SELECT path interpreter driven by a sequence of pivot ranks.
Each recursive call consumes one new rank.  A stochastic implementation obtains
that next rank from the current `Fin xs.length`; keeping the choices explicit
here makes every finite sample path executable and independently testable.
-/
def freshRandomizedSelectWithRanksFuel? :
    Nat → List Nat → Nat → List Nat → Option Nat
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => none
  | fuel + 1, i :: choices, k, xs =>
      match selectByRank? i xs with
      | none => none
      | some pivot =>
          if k < ltCount pivot xs then
            freshRandomizedSelectWithRanksFuel? fuel choices k
              (xs.filter fun y => decide (y < pivot))
          else if k < leCount pivot xs then
            some pivot
          else
            freshRandomizedSelectWithRanksFuel? fuel choices
              (k - leCount pivot xs)
              (xs.filter fun y => decide (pivot < y))

/-- Public rank-choice path interpreter with enough fuel for strict recursion. -/
def freshRandomizedSelectWithRanks? (choices : List Nat)
    (k : Nat) (xs : List Nat) : Option Nat :=
  freshRandomizedSelectWithRanksFuel? xs.length choices k xs

/-! ## Schedule-driven concrete cost semantics -/

/--
Cost of one concrete fresh-rank execution path.  Every visited nonempty state
charges `c * length` and consumes exactly one rank from `choices`.  Running out
of fuel or choices, or presenting a rank outside the current subproblem,
rejects the path instead of silently assigning zero cost.
-/
def randomizedSelectCostWithScheduleFuel :
    Nat → Nat → Nat → List Nat → List Nat → Option Nat
  | 0, _, _, _, _ => none
  | _ + 1, _, _, [], _ => none
  | _ + 1, _, _, _, [] => none
  | fuel + 1, c, k, x :: xs, i :: choices =>
      match selectByRank? i (x :: xs) with
      | none => none
      | some pivot =>
          let here := c * (x :: xs).length
          if k < ltCount pivot (x :: xs) then
            Option.map (here + ·)
              (randomizedSelectCostWithScheduleFuel fuel c k
                ((x :: xs).filter fun y => decide (y < pivot)) choices)
          else if k < leCount pivot (x :: xs) then
            some here
          else
            Option.map (here + ·)
              (randomizedSelectCostWithScheduleFuel fuel c
                (k - leCount pivot (x :: xs))
                ((x :: xs).filter fun y => decide (pivot < y)) choices)

/-- Public schedule cost with one fuel unit for every input occurrence. -/
def randomizedSelectCostWithSchedule
    (c k : Nat) (xs choices : List Nat) : Option Nat :=
  randomizedSelectCostWithScheduleFuel xs.length c k xs choices

/-- Every successful fresh-rank sample path returns the requested order statistic. -/
theorem freshRandomizedSelectWithRanksFuel?_correct :
    ∀ (fuel : Nat) (choices : List Nat) (k : Nat) (xs : List Nat) {x : Nat},
      freshRandomizedSelectWithRanksFuel? fuel choices k xs = some x →
        RankCertificate xs k x := by
  intro fuel
  induction fuel with
  | zero =>
      intro choices k xs x hrun
      simp [freshRandomizedSelectWithRanksFuel?] at hrun
  | succ fuel ih =>
      intro choices k xs selected hrun
      cases choices with
      | nil =>
          simp [freshRandomizedSelectWithRanksFuel?] at hrun
      | cons i choices =>
          cases hpivot : selectByRank? i xs with
          | none =>
              simp [freshRandomizedSelectWithRanksFuel?, hpivot] at hrun
          | some pivot =>
              have hpivotMem : pivot ∈ xs := selectByRank?_mem hpivot
              by_cases hlo : k < ltCount pivot xs
              · have hlow :
                    freshRandomizedSelectWithRanksFuel? fuel choices k
                        (xs.filter fun y => decide (y < pivot)) =
                      some selected := by
                  simpa [freshRandomizedSelectWithRanksFuel?, hpivot, hlo]
                    using hrun
                exact rankCertificate_low_lift (ih choices k _ hlow)
              · by_cases hmid : k < leCount pivot xs
                · have hselected : selected = pivot := by
                    exact Eq.symm (by
                      simpa [freshRandomizedSelectWithRanksFuel?, hpivot, hlo,
                        hmid] using hrun)
                  subst selected
                  exact rankCertificate_pivot hpivotMem hlo hmid
                · have hhigh :
                      freshRandomizedSelectWithRanksFuel? fuel choices
                          (k - leCount pivot xs)
                          (xs.filter fun y => decide (pivot < y)) =
                        some selected := by
                    simpa [freshRandomizedSelectWithRanksFuel?, hpivot, hlo,
                      hmid] using hrun
                  exact rankCertificate_high_lift (Nat.le_of_not_gt hmid)
                    (ih choices (k - leCount pivot xs) _ hhigh)

/-- Correctness of the public fresh-rank path interpreter. -/
theorem freshRandomizedSelectWithRanks?_correct {choices : List Nat}
    {k : Nat} {xs : List Nat} {x : Nat}
    (hrun : freshRandomizedSelectWithRanks? choices k xs = some x) :
    RankCertificate xs k x := by
  exact freshRandomizedSelectWithRanksFuel?_correct xs.length choices k xs
    (by simpa [freshRandomizedSelectWithRanks?] using hrun)

/-- A successful costed path erases to a successful fresh-rank SELECT path. -/
theorem randomizedSelectCostWithScheduleFuel_result :
    ∀ {fuel c k : Nat} {xs choices : List Nat} {cost : Nat},
      randomizedSelectCostWithScheduleFuel fuel c k xs choices = some cost →
        ∃ x, freshRandomizedSelectWithRanksFuel? fuel choices k xs = some x := by
  intro fuel
  induction fuel with
  | zero =>
      intro c k xs choices cost hcost
      simp [randomizedSelectCostWithScheduleFuel] at hcost
  | succ fuel ih =>
      intro c k xs choices cost hcost
      cases xs with
      | nil =>
          simp [randomizedSelectCostWithScheduleFuel] at hcost
      | cons x xs =>
          cases choices with
          | nil =>
              simp [randomizedSelectCostWithScheduleFuel] at hcost
          | cons i choices =>
              cases hpivot : selectByRank? i (x :: xs) with
              | none =>
                  simp [randomizedSelectCostWithScheduleFuel, hpivot] at hcost
              | some pivot =>
                  by_cases hlo : k < ltCount pivot (x :: xs)
                  · cases hrec : randomizedSelectCostWithScheduleFuel fuel c k
                        ((x :: xs).filter fun y => decide (y < pivot)) choices with
                    | none =>
                        simp [randomizedSelectCostWithScheduleFuel, hpivot, hlo,
                          hrec] at hcost
                    | some subcost =>
                        rcases ih hrec with ⟨selected, hselected⟩
                        exact ⟨selected, by
                          simpa [freshRandomizedSelectWithRanksFuel?, hpivot, hlo]
                            using hselected⟩
                  · by_cases hmid : k < leCount pivot (x :: xs)
                    · exact ⟨pivot, by
                        simp [freshRandomizedSelectWithRanksFuel?, hpivot, hlo,
                          hmid]⟩
                    · cases hrec : randomizedSelectCostWithScheduleFuel fuel c
                          (k - leCount pivot (x :: xs))
                          ((x :: xs).filter fun y => decide (pivot < y)) choices with
                      | none =>
                          simp [randomizedSelectCostWithScheduleFuel, hpivot, hlo,
                            hmid, hrec] at hcost
                      | some subcost =>
                          rcases ih hrec with ⟨selected, hselected⟩
                          exact ⟨selected, by
                            simpa [freshRandomizedSelectWithRanksFuel?, hpivot, hlo,
                              hmid] using hselected⟩

/-- A successful public cost execution erases to the public fresh-rank path. -/
theorem randomizedSelectCostWithSchedule_result
    {c k : Nat} {xs choices : List Nat} {cost : Nat}
    (hcost : randomizedSelectCostWithSchedule c k xs choices = some cost) :
    ∃ x, freshRandomizedSelectWithRanks? choices k xs = some x := by
  exact randomizedSelectCostWithScheduleFuel_result
    (by simpa [randomizedSelectCostWithSchedule,
      freshRandomizedSelectWithRanks?] using hcost)

/-- Every successful costed schedule returns a rank-correct SELECT result. -/
theorem randomizedSelectCostWithSchedule_rankCorrect
    {c k : Nat} {xs choices : List Nat} {cost : Nat}
    (hcost : randomizedSelectCostWithSchedule c k xs choices = some cost) :
    ∃ x, RankCertificate xs k x := by
  rcases randomizedSelectCostWithSchedule_result hcost with ⟨x, hx⟩
  exact ⟨x, freshRandomizedSelectWithRanks?_correct hx⟩

/-- Size of the continuation actually selected by one pivot-rank choice. -/
def freshRandomizedSelectContinuationSize (k i : Nat) (xs : List Nat) : Nat :=
  match selectByRank? i xs with
  | none => 0
  | some pivot =>
      if k < ltCount pivot xs then ltCount pivot xs
      else if k < leCount pivot xs then 0
      else gtCount pivot xs

/--
Pointwise coupling to the CLRS larger-side recurrence: for every valid sampled
pivot rank, the continuation actually chosen by the requested order statistic
is no larger than `max i (n - 1 - i)`.
-/
theorem freshRandomizedSelectContinuationSize_le_subproblemSize
    {k i : Nat} {xs : List Nat} (hi : i < xs.length) :
    freshRandomizedSelectContinuationSize k i xs ≤
      subproblemSize xs.length i := by
  rcases selectByRank?_isSome_of_lt hi with ⟨pivot, hpivot⟩
  have hrank : RankCertificate xs i pivot :=
    selectByRank?_rankCorrect hpivot
  by_cases hlo : k < ltCount pivot xs
  · simp only [freshRandomizedSelectContinuationSize, hpivot, hlo, if_pos,
      subproblemSize]
    exact le_trans hrank.2.1 (Nat.le_max_left _ _)
  · by_cases hmid : k < leCount pivot xs
    · simp [freshRandomizedSelectContinuationSize, hpivot, hlo, hmid]
    · simp only [freshRandomizedSelectContinuationSize, hpivot, hlo, hmid,
        if_false, subproblemSize]
      have hhigh : gtCount pivot xs ≤ xs.length - 1 - i := by
        rw [gtCount_eq_length_sub_leCount]
        have hirank : i + 1 ≤ leCount pivot xs :=
          Nat.succ_le_of_lt hrank.2.2
        have hsub := Nat.sub_le_sub_left hirank xs.length
        simpa [Nat.sub_sub, Nat.add_comm] using hsub
      exact le_trans hhigh (Nat.le_max_right _ _)

/--
Expected comparisons of RANDOMIZED-SELECT with an explicit fresh uniform
pivot-rank choice at every recursive call.

The sampled rank `i` ranges uniformly over the current `Fin xs.length`; the
value `selectByRank? i xs` is the corresponding uniformly sampled occurrence
written in rank coordinates.  This is an analysis reindexing of choosing a
uniform input position, not an extra order-statistic computation charged to the
algorithm.  After the partition scan, the expectation recursively averages
again on the selected strict subproblem, so choices at different levels are
fresh rather than a single fixed index reused throughout the run.
-/
noncomputable def freshRandomizedSelectExpectedComparisonsFuel :
    Nat → Nat → List Nat → ℝ
  | 0, _, _ => 0
  | _ + 1, _, [] => 0
  | fuel + 1, k, (x :: xs) =>
      ((x :: xs).length : ℝ) +
        Probability.expect (x :: xs).length (fun i =>
          match selectByRank? i (x :: xs) with
          | none => 0
          | some pivot =>
              if k < ltCount pivot (x :: xs) then
                freshRandomizedSelectExpectedComparisonsFuel fuel k
                  ((x :: xs).filter fun y => decide (y < pivot))
              else if k < leCount pivot (x :: xs) then
                0
              else
                freshRandomizedSelectExpectedComparisonsFuel fuel
                  (k - leCount pivot (x :: xs))
                  ((x :: xs).filter fun y => decide (pivot < y)))

/-- Public fresh-choice expectation, with one unit of fuel per input element. -/
noncomputable def freshRandomizedSelectExpectedComparisons
    (k : Nat) (xs : List Nat) : ℝ :=
  freshRandomizedSelectExpectedComparisonsFuel xs.length k xs

/--
Nested expected cost of fresh-rank RANDOMIZED-SELECT with local charge
`c * length`.  The expectation is taken anew over the current subproblem at
every recursive level; invalid ranks are absent because the sample space has
cardinality equal to the current list length.
-/
noncomputable def randomizedSelectExpectedCostFuel :
    Nat → Nat → Nat → List Nat → Real
  | 0, _, _, _ => 0
  | _ + 1, _, _, [] => 0
  | fuel + 1, c, k, x :: xs =>
      c * ((x :: xs).length : Real) +
        Probability.expect (x :: xs).length fun i =>
          match selectByRank? i (x :: xs) with
          | none => 0
          | some pivot =>
              if k < ltCount pivot (x :: xs) then
                randomizedSelectExpectedCostFuel fuel c k
                  ((x :: xs).filter fun y => decide (y < pivot))
              else if k < leCount pivot (x :: xs) then
                0
              else
                randomizedSelectExpectedCostFuel fuel c
                  (k - leCount pivot (x :: xs))
                  ((x :: xs).filter fun y => decide (pivot < y))

/-- Public expected cost with one fuel unit for every input occurrence. -/
noncomputable def randomizedSelectExpectedCost
    (c k : Nat) (xs : List Nat) : Real :=
  randomizedSelectExpectedCostFuel xs.length c k xs

/-- Exact one-step unfolding of the state-dependent nested expectation. -/
theorem randomizedSelectExpectedCostFuel_succ
    (fuel c k x : Nat) (xs : List Nat) :
    randomizedSelectExpectedCostFuel (fuel + 1) c k (x :: xs) =
      c * ((x :: xs).length : Real) +
        Probability.expect (x :: xs).length (fun i =>
          match selectByRank? i (x :: xs) with
          | none => 0
          | some pivot =>
              if k < ltCount pivot (x :: xs) then
                randomizedSelectExpectedCostFuel fuel c k
                  ((x :: xs).filter fun y => decide (y < pivot))
              else if k < leCount pivot (x :: xs) then
                0
              else
                randomizedSelectExpectedCostFuel fuel c
                  (k - leCount pivot (x :: xs))
                  ((x :: xs).filter fun y => decide (pivot < y))) := by
  rw [randomizedSelectExpectedCostFuel]

/-- Unit local charge recovers the existing fresh-comparison expectation. -/
theorem randomizedSelectExpectedCost_one
    (fuel k : Nat) (xs : List Nat) :
    randomizedSelectExpectedCostFuel fuel 1 k xs =
      freshRandomizedSelectExpectedComparisonsFuel fuel k xs := by
  induction fuel generalizing k xs with
  | zero =>
      simp [randomizedSelectExpectedCostFuel,
        freshRandomizedSelectExpectedComparisonsFuel]
  | succ fuel ih =>
      cases xs with
      | nil =>
          simp [randomizedSelectExpectedCostFuel,
            freshRandomizedSelectExpectedComparisonsFuel]
      | cons x xs =>
          rw [randomizedSelectExpectedCostFuel,
            freshRandomizedSelectExpectedComparisonsFuel]
          simp only [Nat.cast_one, one_mul]
          congr 1
          apply congrArg (Probability.expect (x :: xs).length)
          funext i
          cases hpivot : selectByRank? i (x :: xs) with
          | none =>
              simp
          | some pivot =>
              by_cases hlo : k < ltCount pivot (x :: xs)
              · simp [hlo, ih]
              · by_cases hmid : k < leCount pivot (x :: xs)
                · simp [hlo, hmid]
                · simp [hlo, hmid, ih]

/-- The nested fresh-choice expected cost is nonnegative. -/
theorem randomizedSelectExpectedCost_nonneg
    (fuel c k : Nat) (xs : List Nat) :
    0 ≤ randomizedSelectExpectedCostFuel fuel c k xs := by
  induction fuel generalizing c k xs with
  | zero =>
      simp [randomizedSelectExpectedCostFuel]
  | succ fuel ih =>
      cases xs with
      | nil =>
          simp [randomizedSelectExpectedCostFuel]
      | cons x xs =>
          rw [randomizedSelectExpectedCostFuel]
          apply add_nonneg (by positivity)
          apply Probability.expect_nonneg
          intro i
          cases selectByRank? i (x :: xs) with
          | none =>
              simp
          | some pivot =>
              by_cases hlo : k < ltCount pivot (x :: xs)
              · simpa [hlo] using ih c k
                  ((x :: xs).filter fun y => decide (y < pivot))
              · by_cases hmid : k < leCount pivot (x :: xs)
                · simp [hlo, hmid]
                · simpa [hlo, hmid] using ih c
                    (k - leCount pivot (x :: xs))
                    ((x :: xs).filter fun y => decide (pivot < y))

/--
The actual recursive continuation selected at pivot rank `i` is bounded by the
larger-side term `max i (n-1-i)` used in the CLRS majorizing recurrence.
Consequently the fresh-choice stochastic execution has expected comparison
cost at most `4n`.
-/
theorem freshRandomizedSelectExpectedComparisonsFuel_linear_bound :
    ∀ (fuel k : Nat) (xs : List Nat),
      freshRandomizedSelectExpectedComparisonsFuel fuel k xs ≤
        4 * (xs.length : ℝ) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k xs
      simp [freshRandomizedSelectExpectedComparisonsFuel]
  | succ fuel ih =>
      intro k xs
      cases xs with
      | nil =>
          simp [freshRandomizedSelectExpectedComparisonsFuel]
      | cons x xs =>
          let ys := x :: xs
          let X : Nat → ℝ := fun i =>
            match selectByRank? i ys with
            | none => 0
            | some pivot =>
                if k < ltCount pivot ys then
                  freshRandomizedSelectExpectedComparisonsFuel fuel k
                    (ys.filter fun y => decide (y < pivot))
                else if k < leCount pivot ys then
                  0
                else
                  freshRandomizedSelectExpectedComparisonsFuel fuel
                    (k - leCount pivot ys)
                    (ys.filter fun y => decide (pivot < y))
          have hterm : ∀ i ∈ Finset.range ys.length,
              X i ≤ 4 * ((max i (xs.length - i) : Nat) : ℝ) := by
            intro i hi
            have hiLt : i < ys.length := Finset.mem_range.mp hi
            rcases selectByRank?_isSome_of_lt hiLt with ⟨pivot, hpivot⟩
            have hrank : RankCertificate ys i pivot :=
              selectByRank?_rankCorrect hpivot
            simp only [X, hpivot]
            by_cases hlo : k < ltCount pivot ys
            · simp only [hlo, if_pos]
              have hrec := ih k (ys.filter fun y => decide (y < pivot))
              have hsize :
                  (ys.filter fun y => decide (y < pivot)).length ≤
                    max i (xs.length - i) := by
                exact le_trans hrank.2.1 (Nat.le_max_left _ _)
              have hcast :
                  4 * ((ys.filter fun y => decide (y < pivot)).length : ℝ) ≤
                    4 * ((max i (xs.length - i) : Nat) : ℝ) := by
                exact_mod_cast Nat.mul_le_mul_left 4 hsize
              exact le_trans hrec hcast
            · by_cases hmid : k < leCount pivot ys
              · simp [hlo, hmid]
              · simp only [hlo, hmid, if_false]
                have hrec := ih (k - leCount pivot ys)
                  (ys.filter fun y => decide (pivot < y))
                have hhigh : gtCount pivot ys ≤ xs.length - i := by
                  rw [gtCount_eq_length_sub_leCount]
                  have hirank : i < leCount pivot ys := hrank.2.2
                  have hlenys : ys.length = xs.length + 1 := by simp [ys]
                  omega
                have hsize :
                    (ys.filter fun y => decide (pivot < y)).length ≤
                      max i (xs.length - i) := by
                  exact le_trans hhigh (Nat.le_max_right _ _)
                have hcast :
                    4 * ((ys.filter fun y => decide (pivot < y)).length : ℝ) ≤
                      4 * ((max i (xs.length - i) : Nat) : ℝ) := by
                  exact_mod_cast Nat.mul_le_mul_left 4 hsize
                exact le_trans hrec hcast
          have hsum :
              (∑ i ∈ Finset.range ys.length, X i) ≤
                4 * (∑ i ∈ Finset.range ys.length,
                  ((max i (xs.length - i) : Nat) : ℝ)) := by
            calc
              (∑ i ∈ Finset.range ys.length, X i) ≤
                  ∑ i ∈ Finset.range ys.length,
                    4 * ((max i (xs.length - i) : Nat) : ℝ) :=
                Finset.sum_le_sum hterm
              _ = 4 * (∑ i ∈ Finset.range ys.length,
                    ((max i (xs.length - i) : Nat) : ℝ)) := by
                rw [Finset.mul_sum]
          have hmax :
              4 * (∑ i ∈ Finset.range ys.length,
                  ((max i (xs.length - i) : Nat) : ℝ)) ≤
                3 * (ys.length : ℝ) ^ 2 := by
            simpa [ys, Nat.cast_add, Nat.cast_one] using
              sum_maxSide_real_bound xs.length
          have hsumBound :
              (∑ i ∈ Finset.range ys.length, X i) ≤
                3 * (ys.length : ℝ) ^ 2 := le_trans hsum hmax
          have hlenPos : (0 : ℝ) < (ys.length : ℝ) := by
            have hnat : 0 < ys.length := by simp [ys]
            exact_mod_cast hnat
          have hfrac :
              (∑ i ∈ Finset.range ys.length, X i) / (ys.length : ℝ) ≤
                3 * (ys.length : ℝ) := by
            apply (div_le_iff₀ hlenPos).2
            nlinarith
          change (ys.length : ℝ) + Probability.expect ys.length X ≤
            4 * (ys.length : ℝ)
          unfold Probability.expect
          linarith

/--
Fresh-choice RANDOMIZED-SELECT has expected linear comparison cost on every
input and requested rank: `E[C] ≤ 4n`.
-/
theorem freshRandomizedSelectExpectedComparisons_linear_bound
    (k : Nat) (xs : List Nat) :
    freshRandomizedSelectExpectedComparisons k xs ≤ 4 * (xs.length : ℝ) := by
  exact freshRandomizedSelectExpectedComparisonsFuel_linear_bound xs.length k xs

/-! ## Rank correctness via a randomized pivot oracle -/

/--
Pivot oracle that selects the element at a designated index, reusing the
pivot-parametric SELECT skeleton of Section 9.3.  Fixing one index does not by
itself model fresh random choices across recursive calls.
-/
def pivotAtIndex? (i : ℕ) (xs : List ℕ) : Option ℕ := xs[i]?

/-- The index pivot oracle only ever returns members of its input list. -/
theorem pivotAtIndex?_mem (i : ℕ) : PivotMembership (pivotAtIndex? i) := by
  intro xs pivot hsel
  rcases getElem?_eq_some_iff_split.mp hsel with ⟨lo, hi, rfl, _hlen⟩
  simp

/--
SELECT with the pivot chosen at a fixed index `i`, obtained by instantiating the
pivot-parametric selector {lit}`CLRS.Chapter09.selectWithPivot?`.  This is a
deterministic specialization used only for conditional rank correctness; it
does not model the fresh per-call choices of `RANDOMIZED-SELECT`.
-/
def randomizedSelectAtIndex? (i k : ℕ) (xs : List ℕ) : Option ℕ :=
  selectWithPivot? (pivotAtIndex? i) k xs

/--
Rank correctness of the fixed-index specialization is inherited from the
pivot-parametric skeleton: any successful result is a valid zero-based order
statistic.
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

end Chapter09
end CLRS
