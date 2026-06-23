import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_03.Section_03_2_Standard_Functions

/-!
# Chapter 3. Growth of Functions

CLRS introduces asymptotic notation — O, Ω, Θ, o, ω — as the language for
describing how running times grow with input size.  This chapter bridges the
textbook definitions to mathlib's filter-based asymptotics library.

## 3.1 Asymptotic Notation

Defines O, Ω, Θ, o, ω as CLRS-style wrappers around mathlib's
`=O[atTop]` / `=o[atTop]`.  Proves equivalence between the CLRS discrete
definition (`∃ c n₀`) and the filter-based one.  Collects algebraic
properties: reflexivity, transitivity, sum and product rules.

## 3.2 Standard Functions

Proves concrete growth comparisons that matter for algorithm analysis:
* polynomial `n^a` vs exponential `2^n`
* logarithm `log n` vs polynomial `n^ε`
* factorial lower and upper bounds
* floor / ceiling Θ-behavior

Notation: we use `|·|` (absolute value) rather than `‖·‖` for readability.
-/

namespace CLRS
namespace Chapter03
end Chapter03
end CLRS
