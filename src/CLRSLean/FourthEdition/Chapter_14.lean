import CLRSLean.FourthEdition.Chapter_14.Section_14_2_Matrix_Chain_Multiplication.Execution
import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming.Execution
import CLRSLean.FourthEdition.Chapter_14.Section_14_5_Optimal_Binary_Search_Trees.Execution
import CLRSLean.Chapter_15
import CLRSLean.FourthEdition.Chapter_14.Section_14_1_Rod_Cutting
import CLRSLean.FourthEdition.Chapter_14.Section_14_2_Matrix_Chain_Multiplication
import CLRSLean.FourthEdition.Chapter_14.Section_14_3_Elements_Of_Dynamic_Programming
import CLRSLean.FourthEdition.Chapter_14.Section_14_4_Longest_Common_Subsequence
import CLRSLean.FourthEdition.Chapter_14.Section_14_5_Optimal_Binary_Search_Trees

/-!
# Chapter 14 — Dynamic Programming

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 14.1–14.5 separate mathematical recurrences from stored-state
executions with correctness and actual event counters:

* [Section 14.1 — Rod cutting](CLRSLean/FourthEdition/Chapter_14/Section_14_1_Rod_Cutting/):
  optimal-cut reconstruction and top-down cache-value correctness; a counted
  bottom-up array fill performs exactly `n(n+1)/2` candidate evaluations and
  `n+1` writes. This counter does not measure the separate top-down evaluator.
* [Section 14.2 — Matrix-chain multiplication](CLRSLean/FourthEdition/Chapter_14/Section_14_2_Matrix_Chain_Multiplication/):
  actual interval rows of costs/splits, stored-split reconstruction, recurrence
  refinement, and executed cell/candidate counters.
* [Section 14.3 — Elements of dynamic programming](CLRSLean/FourthEdition/Chapter_14/Section_14_3_Elements_Of_Dynamic_Programming/):
  a reusable append-only row builder, dependency-order invariant, and counters,
  instantiated by matrix-chain and optimal BST. The older distinct-cache
  cardinality inequality alone is not an execution guarantee.
* [Section 14.4 — Longest common subsequence](CLRSLean/FourthEdition/Chapter_14/Section_14_4_Longest_Common_Subsequence/):
  rolling-row length computation equal to the recursive specification, with
  exactly `(m+1)(n+1)` visited cells and a returned row of length `n+1`.
  Legacy reconstruction still uses the recursive oracle and has no such time bound.
* [Section 14.5 — Optimal binary search trees](CLRSLean/FourthEdition/Chapter_14/Section_14_5_Optimal_Binary_Search_Trees/):
  stored cost/weight/root rows, cached weight updates, and reconstruction from
  stored roots, for nonnegative integer weights (not general real probabilities).

Declarations keep their legacy {lit}`CLRS.Chapter15` namespaces; the
third-edition-numbered imports {lit}`CLRSLean.Chapter_15` and
{lit}`CLRSLean.Chapter_15.Section_15_*` forward to these sources during the
compatibility period.

## Coverage boundary

The counted executions operate on stored predecessors, with constant many
primitive operations per visited cell/candidate. The cost model excludes
allocation/copying internals, key equality internals, and arithmetic bit costs.
The legacy recursive functions remain mathematical reference specifications;
their value correctness does not establish tabulated runtime. Cell counts and
stored row sizes are not peak-memory or call-stack bounds.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
