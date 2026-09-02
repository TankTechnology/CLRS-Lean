import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Core
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Hardness

/-!
# 34.3 NP-Completeness and Reducibility

CLRS §34.3: polynomial-time reducibility and the definitions of NP-hard and
NP-complete languages.

Main results:

- Definition `PolyTimeReducible`: `L₁ ≤_P L₂` — a polynomial-time computable
  reduction maps `L₁` into `L₂`.
- Definition `NPHard`: every polynomially verifiable language reduces to `L`.
- Definition `NPComplete`: `L ∈ NP` and `L` is NP-hard.
- Theorem `PolyTimeReducible.trans`: `≤_P` is transitive (via the composition
  of polynomial-time machines).
- Theorems `PolyTimeDecidable.of_reducible`, `NPHard.of_reducible`, and
  `NPComplete.of_reducible`: reductions transport decidability and hardness.
- Theorems `NPComplete.verifiable` and `NPComplete.hard`: direct projections
  from NP-completeness.
-/
