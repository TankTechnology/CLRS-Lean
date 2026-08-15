import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability

/-!
# CLRS Section 7.4 - Analysis of quicksort

This section presents the expected running-time analysis of randomized
quicksort (CLRS §7.4), building on the expected-comparison development of §7.3.
The dominant cost of quicksort is comparisons: every other operation performs
`O(1)` work per comparison, so the running time is (up to a constant factor)
the number of comparisons.  The analysis therefore bounds the expected number
of comparisons `E[X]`.

The proof is the indicator-variable argument of CLRS §7.4.2: writing
{lit}`X_ij` for the indicator that the `i`-th and `j`-th smallest elements are
ever compared, linearity of expectation gives
{lit}`E[X] = Σ_{i<j} P[z_i and z_j are compared]`, and the comparison
probability is {lit}`2/(j - i + 1)` (CLRS Lemma 7.1, proved in the §7.3
comparison-probability file).  Summing over all pairs yields the closed form
{lit}`2(n+1) H_n - 4n`, which is {lit}`Θ(n log n)` (CLRS Theorem 7.1).

Main results:

- Definition {lit}`expectedRunningTime`: the expected running time of randomized
  quicksort on `n` elements, identified with the expected number of
  comparisons.
- Theorem {lit}`expectedRunningTime_eq_sum_compared_prob`: the indicator
  decomposition `E[X] = Σ_{i<j} 2/(j-i+1)`.
- Theorem {lit}`expectedRunningTime_le_two_mul`: `E[X] ≤ 2n·H_n`, an explicit
  `O(n log n)` upper bound.
- Theorem {lit}`expectedRunningTime_isBigTheta_nlogn`: `E[X] = Θ(n log n)`
  (CLRS Theorem 7.1).

Notation conventions used in this section:

- `n` : the number of elements
- `X` : the number of comparisons
- `H_n` : the `n`-th harmonic number ({lit}`harmonic n`)
- `expectedRunningTime`, `E[X]` : the expected running time / comparisons
-/

namespace CLRS
namespace Chapter07

/--
The expected running time of randomized quicksort on `n` elements.  Each
comparison performs `O(1)` work and dominates all other operations, so the
running time is, up to a constant factor, the number of comparisons.  We take
the expected number of comparisons `E[X]` as the expected running time,
matching CLRS §7.4.2.
-/
noncomputable def expectedRunningTime (n : ℕ) : ℝ := expectedComparisonsReal n

/--
**Indicator decomposition (CLRS §7.4.2).**  Let `X` be the number of
comparisons and `X_ij` the indicator that the `i`-th and `j`-th smallest
elements are ever compared.  By linearity of expectation,
`E[X] = Σ_{i<j} P[z_i and z_j are compared]`, and by CLRS Lemma 7.1 the
comparison probability is `2/(j - i + 1)`.  This connects the probability model
to the algebraic closed form `expectedComparisons n`.
-/
theorem expectedRunningTime_eq_sum_compared_prob (n : ℕ) :
    expectedRunningTime n =
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i < j then (2 : ℝ) / ((j - i + 1 : ℕ) : ℝ) else 0) := by
  have h := sum_compared_prob_eq_expectedComparisons n
  dsimp [expectedRunningTime, expectedComparisonsReal]
  rw [← h]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x < i
  · rw [if_pos hxi, if_pos hxi]
    norm_num
  · rw [if_neg hxi, if_neg hxi]
    norm_num

/--
An explicit `O(n log n)` upper bound on the expected running time:
`E[X] ≤ 2n·H_n`, where `H_n` is the `n`-th harmonic number.
-/
theorem expectedRunningTime_le_two_mul (n : ℕ) :
    expectedRunningTime n ≤ 2 * (n : ℝ) * (harmonic n : ℝ) := by
  unfold expectedRunningTime
  exact expectedComparisons_harmonic_bound_real n

/--
**Expected running time of randomized quicksort (CLRS Theorem 7.1).**  On `n`
elements, the expected running time is `Θ(n log n)`: the expected number of
comparisons `E[X]` is asymptotically `n·log n`, since the harmonic upper bound
`2n·H_n` and the corresponding lower bound are both `Θ(n log n)`.
-/
theorem expectedRunningTime_isBigTheta_nlogn :
    CLRS.Chapter03.isBigTheta expectedRunningTime (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  unfold expectedRunningTime
  exact expectedComparisons_isBigTheta_nlogn

end Chapter07
end CLRS
