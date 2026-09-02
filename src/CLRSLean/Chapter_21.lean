import CLRSLean.Chapter_21.Section_21_1_Disjoint_Set_Operations
import CLRSLean.Chapter_21.Section_21_2_Linked_List_Representation
import CLRSLean.Chapter_21.Section_21_3_Disjoint_Set_Forests
import CLRSLean.Chapter_21.Section_21_4_Analysis
import CLRSLean.Chapter_21.Section_21_4_Analysis.CostedExecution
import CLRSLean.Chapter_21.Section_21_4_Analysis.InverseAckermann

/-!
# Chapter 21 - Data Structures for Disjoint Sets

Chapter 21 formalizes the abstract partition semantics of {lit}`MAKE-SET`,
{lit}`FIND-SET`, and {lit}`UNION`, followed by executable representations and
their correctness and complexity arguments.

## Current sections

* 21.1 Disjoint-set operations: {lit}`proved`.  The abstract partition model,
  exact merge semantics, and operation-trace monotonicity are proved.
* 21.2 Linked-list representation: {lit}`proved` for table-level functional
  correctness and the weighted-union {lit}`O(n log n)` rewrite bound.
* 21.3 Disjoint-set forests: {lit}`proved` for functional correctness.  The
  Batteries union-by-rank/path-compression implementation is proved to refine
  the abstract model, including the executable equivalence query.
* 21.4 Rank and path-compression analysis: {lit}`proved`.  Real Batteries
  parent traversals are counted, rank mass is proved for every reachable
  state, the Ackermann level/index potential is instantiated, and concrete
  executions satisfy {lit}`O((m+n) alpha(n))`, hence {lit}`O(m alpha(n))`
  under the standard {lit}`n <= m` assumption.

The represented chapter's main functional-correctness and amortized-complexity
stack is complete.  Lower-level array-write/RAM constants and a stateful
Chapter 23 Kruskal scan remain separate implementation refinements.
-/

namespace CLRS
namespace Chapter21
end Chapter21
end CLRS
