import CLRSLean.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# Chapter 12 - Binary Search Trees

Chapter 12 studies binary search trees and the operations that preserve their
ordering invariant.  The current CLRS-Lean pass uses an inductive tree of natural
keys and proves search, minimum/maximum, insertion, functional
successor/predecessor, and functional deletion correctness for membership and
ordering.

## Sections

* 12.1 Binary search trees: {lit}`partial`, with the functional BST theorem
  boundary complete for the current inductive-tree model.
  Main results: {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.successor?_least_greater`,
  {lit}`CLRS.Chapter12.BSTree.successor?_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`,
  {lit}`CLRS.Chapter12.BSTree.inTree_delete_iff`,
  {lit}`CLRS.Chapter12.BSTree.not_inTree_delete_self`,
  {lit}`CLRS.Chapter12.BSTree.delete_eq_self_of_not_inTree`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_self_eq_false`,
  {lit}`CLRS.Chapter12.BSTree.delete_ordered`.

## Current Gaps

Functional successor/predecessor queries and functional deletion are formalized.
Parent-pointer successor/predecessor procedures, transplant, and pointer-level
mutation are not yet formalized.  The pointer-transplant algorithm from CLRS
needs an imperative tree model or a refinement from the functional deletion
theorem.
-/

namespace CLRS
namespace Chapter12
end Chapter12
end CLRS
