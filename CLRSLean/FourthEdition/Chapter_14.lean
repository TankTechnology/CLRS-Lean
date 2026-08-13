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

Sections 14.1–14.5 are native fourth-edition sections that complete the
algorithm boundary on top of the legacy recurrence sources:

* [Section 14.1 — Rod cutting](CLRSLean/FourthEdition/Chapter_14/Section_14_1_Rod_Cutting/):
  optimal-cut reconstruction, top-down memoization, and the `O(n²)` step count.
* [Section 14.2 — Matrix-chain multiplication](CLRSLean/FourthEdition/Chapter_14/Section_14_2_Matrix_Chain_Multiplication/):
  the tabulated `MATRIX-CHAIN-ORDER` and its `Θ(n³)` / `Θ(n²)` bounds.
* [Section 14.3 — Elements of dynamic programming](CLRSLean/FourthEdition/Chapter_14/Section_14_3_Elements_Of_Dynamic_Programming/):
  the reusable memo-cache invariant and distinct-state cost bridge.
* [Section 14.4 — Longest common subsequence](CLRSLean/FourthEdition/Chapter_14/Section_14_4_Longest_Common_Subsequence/):
  the tabulated `Θ(mn)` LCS bound.
* [Section 14.5 — Optimal binary search trees](CLRSLean/FourthEdition/Chapter_14/Section_14_5_Optimal_Binary_Search_Trees/):
  the public e/w/root tables, reconstruction, and cost bounds.

Declarations keep their legacy {lit}`CLRS.Chapter15` namespaces; the
third-edition-numbered imports {lit}`CLRSLean.Chapter_15` and
{lit}`CLRSLean.Chapter_15.Section_15_*` forward to these sources during the
compatibility period.

## Coverage boundary

The native sections close the §14.1–14.5 boundary.  An explicit RAM execution
cost semantics (as opposed to the step-count and table bounds) remains a future
implementation-level target.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
