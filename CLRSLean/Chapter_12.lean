import CLRSLean.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# Chapter 12 - Binary Search Trees

Chapter 12 studies binary search trees and the operations that preserve their
ordering invariant.  The current CLRSLean pass uses an inductive tree of natural
keys and proves insertion correctness for membership and ordering.

## Sections

* 12.1 Binary search trees: `partial`.
  Main results: {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`.

## Current Gaps

Tree search, minimum/maximum, predecessor/successor, and deletion are not yet
formalized.  The pointer-transplant algorithm from CLRS needs an imperative
tree model or a separate functional deletion theorem.
-/

namespace CLRS
namespace Chapter12
end Chapter12
end CLRS
