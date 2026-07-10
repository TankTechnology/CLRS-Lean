import CLRSLean.Chapter_21.Section_21_1_Disjoint_Set_Operations
import CLRSLean.Chapter_21.Section_21_2_Linked_List_Representation
import CLRSLean.Chapter_21.Section_21_3_Disjoint_Set_Forests
import CLRSLean.Chapter_21.Section_21_4_Analysis
import CLRSLean.Chapter_21.Section_21_4_Analysis.CostedExecution

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
* 21.4 Rank and path-compression analysis: {lit}`partial`.  Real Batteries
  parent traversals are counted, rank-mass is proved for every reachable
  state, whole executions refine the abstract trace, and the concrete
  {lit}`O(m log n)` bound is proved.  Instantiating the inverse-Ackermann
  potential certificate remains the sharper strengthening target.

The represented chapter is complete for functional correctness and now has a
concrete logarithmic execution bound.  The sharper RAM-level
{lit}`O(m α(n))` refinement is kept explicit as the remaining complexity
boundary.
-/

namespace CLRS
namespace Chapter21
end Chapter21
end CLRS
