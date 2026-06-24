import CLRSLean.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# Chapter 12 - Binary Search Trees

Chapter 12 studies binary search trees and the operations that preserve their
ordering invariant.  The current CLRS-Lean pass uses an inductive tree of natural
keys and proves search, minimum/maximum, and insertion correctness for
membership and ordering.  It now also proves functional successor/predecessor
queries over the same ordered-tree model.

## Sections

* 12.1 Binary search trees: `partial`.
  Main results: {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.successor?_least_greater`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`.

## Current Gaps

The functional successor/predecessor queries are formalized.  Parent-pointer
successor/predecessor procedures, transplant, and deletion are not yet
formalized.  The pointer-transplant algorithm from CLRS needs an imperative tree
model or a separate functional deletion theorem.
-/

namespace CLRS
namespace Chapter12
end Chapter12
end CLRS
