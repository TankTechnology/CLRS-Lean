import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_03.Section_03_2_Standard_Functions

/-!
# Chapter 3. Growth of Functions

CLRS introduces asymptotic notation — O, Ω, Θ, o, ω — as the language for
describing how running times grow with input size.  This chapter bridges the
textbook definitions to mathlib's filter-based asymptotics library.

## 3.1 Asymptotic Notation

Defines O, Ω, Θ, o, ω as CLRS-style wrappers around mathlib's
{lit}`=O[atTop]` / {lit}`=o[atTop]`.  Proves equivalence between the CLRS discrete
definition ({lit}`∃ c n₀`) and the filter-based one.  Collects algebraic
properties: reflexivity, transitivity, sum and product rules.

## 3.2 Standard Functions

Proves concrete growth comparisons that matter for algorithm analysis:
* polynomial {lit}`n^a` vs exponential {lit}`c^n` for every {lit}`c > 1`
* logarithm powers {lit}`(log n)^a` vs polynomial {lit}`n^ε`
* exponential base comparisons {lit}`a^n = o(b^n)` for {lit}`0 ≤ a < b`
* harmonic numbers {lit}`H_n ~ log n` and {lit}`H_n = Θ(log n)`
* factorial upper/lower bounds, exponential-vs-factorial comparison, and
  {lit}`n! = o(n^n)`
* floor / ceiling Θ-behavior, including half-scale floor and ceiling
* Fibonacci-number growth: Binet's closed form {lit}`F_n = (φ^n − ψ^n)/√5`,
  {lit}`F_n = Θ(φ^n)`, and the closest-integer bound {lit}`|φ^n/√5 − F_n| < 1/2`
* the iterated logarithm {lit}`lg* n`: definition by well-founded recursion, the
  tower recurrence {lit}`lg*(2^n) = 1 + lg* n`, monotonicity, {lit}`lg* n ≤ log₂ n + 1`,
  and the extreme slow growth {lit}`lg* n = o(log n)`

Notation: we use {lit}`|·|` (absolute value) rather than {lit}`‖·‖` for readability.
-/

namespace CLRS
namespace Chapter03
end Chapter03
end CLRS
