import CLRSLean.Chapter_34.Section_34_1_3_NP_Foundations
import CLRSLean.Chapter_34.Section_34_4_5_NP_Completeness

/-!
# Chapter 34 — NP-Completeness

Chapter 34 of CLRS introduces the theory of NP-completeness: the classes P and NP,
polynomial-time reducibility, and the central question of whether P = NP.
This chapter formalizes the core definitions and the classic reduction chain
showing that CIRCUIT-SAT, SAT, 3-CNF-SAT, CLIQUE, and VERTEX-COVER are all
NP-complete.

## Sections

* §34.1–34.3 — NP Foundations: `def-complete`.
  Core definitions:
  {lit}`CLRS.Chapter34.DecisionProblem`,
  {lit}`CLRS.Chapter34.polyTime`,
  {lit}`CLRS.Chapter34.ClassP`,
  {lit}`CLRS.Chapter34.ClassNP`,
  {lit}`CLRS.Chapter34.polyReducesTo` (reducibility),
  {lit}`CLRS.Chapter34.NP_hard`,
  {lit}`CLRS.Chapter34.NP_complete`.

  Core theorems:
  {lit}`CLRS.Chapter34.P_subset_NP` (Lemma 34.1),
  {lit}`CLRS.Chapter34.polyReducesTo_trans` (Lemma 34.3),
  {lit}`CLRS.Chapter34.NP_complete_polyTime_implies_P_eq_NP` (Lemma 34.8).

* §34.4–34.5 — NP-Complete Problems: `def-complete`.
  Problems defined:
  {lit}`CLRS.Chapter34.CIRCUIT_SAT`,
  {lit}`CLRS.Chapter34.SAT`,
  {lit}`CLRS.Chapter34.THREE_CNF_SAT`,
  {lit}`CLRS.Chapter34.CLIQUE`,
  {lit}`CLRS.Chapter34.VERTEX_COVER`.

  Reduction chain (Theorems 34.9–34.12, statements only):
  {lit}`CLRS.Chapter34.circuit_sat_reduces_to_sat`,
  {lit}`CLRS.Chapter34.sat_reduces_to_3cnf_sat`,
  {lit}`CLRS.Chapter34.three_cnf_sat_reduces_to_clique`,
  {lit}`CLRS.Chapter34.clique_reduces_to_vertex_cover`.

## Current State

The foundational definitions (§34.1–34.3) are complete at the **type level**:
`polyTime` is a placeholder predicate (`True`), so the statements of
`P ⊆ NP`, transitivity of `≤_P`, and Lemma 34.8 all go through.  A real
complexity treatment requires defining a computational model (e.g., Turing
machines or a cost-aware monad) and replacing the `polyTime` placeholder
with a genuine runtime-bound predicate.

The problem definitions and reduction chain theorems (§34.4–34.5) are
**statement-complete**.  The reduction functions (Tseitin transformation,
clause-expansion, formula-graph construction, complement-graph construction)
are declared as `sorry`; filling them in is future work.

## Pending Work

* Define a formal polynomial-time predicate (Turing-machine model or
  cost monad) to replace `polyTime := True`.
* Construct the four reduction functions (Theorems 34.9–34.12) and prove
  their correctness and polynomial-time bounds.
* Prove that CIRCUIT-SAT is in NP (easy) and NP-hard (requires Cook-Levin,
  a major undertaking).
* Extend to further NP-complete problems: SUBSET-SUM, HAM-CYCLE, TSP, etc.

## References

* CLRS 4th Edition, Chapter 34
* [Complexity Zoo](https://complexityzoo.net/)
* [Cook-Levin theorem on Wikipedia](https://en.wikipedia.org/wiki/Cook%E2%80%93Levin_theorem)
-/

namespace CLRS
namespace Chapter34

end Chapter34
end CLRS
