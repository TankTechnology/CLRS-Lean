import CLRSLean.Chapter_05.Section_05_1_Hiring_Problem
import CLRSLean.Chapter_05.Section_05_2_Indicator_Random_Variables
import CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis

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

Section 5.4 applies indicators plus independence to two classic probabilistic
analyses: the **birthday paradox** (expected number of same-birthday pairs is
{lit}`k(k-1)/(2n)`) and **balls and bins** (expected number of balls in a fixed
bin is {lit}`k/n`).

* Section 5.1: {lit}`proved` for the finite rank-symmetry model, including
  {lit}`CLRS.Chapter05.expectedHires_isBigTheta_log`.
* Section 5.2: {lit}`proved` for the uniform-permutation model, including
  {lit}`CLRS.Chapter05.expectedFixedPoints_eq_one`.
* Section 5.4: {lit}`proved` for the product-uniform model, including
  {lit}`CLRS.Chapter05.expectedCollisions_eq` and
  {lit}`CLRS.Chapter05.expectedBallsInBin_eq`.
-/

namespace CLRS
namespace Chapter05
end Chapter05
end CLRS
