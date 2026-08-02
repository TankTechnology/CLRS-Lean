import CLRSLean.Chapter_05.Section_05_1_Hiring_Problem
import CLRSLean.Chapter_05.Section_05_2_Indicator_Random_Variables
import CLRSLean.Chapter_05.Section_05_3_Randomized_Algorithms
import CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis
import CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis.OnlineHiring

/-!
# Chapter 5. Probabilistic Analysis and Randomized Algorithms

The hiring problem studies the expected number of times a new best candidate is
hired in a random interview order.  Section 5.1 proves the finite rank-symmetry
calculation that the step probability is {lit}`1/(n+1)`, sums the indicator
expectations, proves the equivalent recurrence solution, and derives the
logarithmic asymptotic growth of the expected number of hires.

Section 5.2 formalizes the **indicator random variable** technique and
**linearity of expectation** with the **hat-check problem** (expected fixed
points of a uniform random permutation of {lit}`Fin n` equal {lit}`1`).

Section 5.3 proves the central result of CLRS §5.3: the `RANDOMIZE-IN-PLACE`
procedure (Fisher–Yates shuffle) yields a uniform random permutation of
{lit}`Fin n` (Lemma 5.5), modelled by an explicit choice-vector sample space
and a bijection onto {lit}`Equiv.Perm (Fin n)`.

Section 5.4 applies indicators plus independence to two classic probabilistic
analyses: the **birthday paradox** (expected number of same-birthday pairs is
{lit}`k(k-1)/(2n)`) and **balls and bins** (expected number of balls in a fixed
bin is {lit}`k/n`).  It also proves the **longest streak** result that the
expected longest run of heads in {lit}`n` fair coin flips is
{lit}`Θ(log n)` — upper bound {lit}`E[L] ≤ log₂ n + 2` and lower bound
{lit}`E[L] ≥ log₂ n / 8` for {lit}`n ≥ 16`.  Its on-line hiring model provides
an executable threshold strategy over finite permutations, the finite success
probability {lit}`CLRS.Chapter05.OnlineHiring.probHireBest`, its harmonic
closed form {lit}`(k/n)(H_{n-1} - H_{k-1})`, and the asymptotic {lit}`1/e`
success probability for the threshold {lit}`⌊n/e⌋`.

* Section 5.1: {lit}`proved` for the finite rank-symmetry model, including
  {lit}`CLRS.Chapter05.expectedHires_isBigTheta_log`.
* Section 5.2: {lit}`proved` for the uniform-permutation model, including
  {lit}`CLRS.Chapter05.expectedFixedPoints_eq_one`.
* Section 5.3: {lit}`proved` for the independent-swap-choice model, including
  {lit}`CLRS.Chapter05.randomizeInPlace_uniform` (Lemma 5.5).
* Section 5.4: {lit}`proved` for the product-uniform birthday and balls-and-bins
  models ({lit}`CLRS.Chapter05.expectedCollisions_eq`,
  {lit}`CLRS.Chapter05.expectedBallsInBin_eq`), the longest-streak
  {lit}`Θ(log n)` bounds
  ({lit}`CLRS.Chapter05.expectedLongestStreak_le`,
  {lit}`CLRS.Chapter05.expectedLongestStreak_lowerBound`), and on-line hiring,
  whose success probability has the harmonic closed form
  ({lit}`CLRS.Chapter05.OnlineHiring.probHireBest_eq`) and the {lit}`1/e`
  asymptotic ({lit}`CLRS.Chapter05.OnlineHiring.probHireBest_asymptotic`).
-/

namespace CLRS
namespace Chapter05
end Chapter05
end CLRS
