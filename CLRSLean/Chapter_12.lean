import CLRSLean.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# Chapter 12 - Binary Search Trees

Chapter 12 studies binary search trees and the operations that preserve their
ordering invariant.  The current CLRS-Lean pass uses an inductive tree of natural
keys and proves search, minimum/maximum, insertion, functional
successor/predecessor, and functional deletion correctness for membership and
ordering.  A zipper refinement represents the path to the current node as a
functional parent-pointer context and proves iterative search, subtree
transplant, deletion through that transplant interface, and parent-ascent
successor/predecessor equivalent to the established functional operations.

## Sections

* 12.1 Binary search trees: {lit}`partial`, with the functional BST theorem and
  zipper-based parent-navigation boundaries complete for the current
  inductive-tree model.
  Main results: {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.successor?_least_greater`,
  {lit}`CLRS.Chapter12.BSTree.successor?_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_isSome_iff_exists_greater`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_isSome_iff_exists_less`,
  {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.search_insert_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`,
  {lit}`CLRS.Chapter12.BSTree.inTree_delete_iff`,
  {lit}`CLRS.Chapter12.BSTree.not_inTree_delete_self`,
  {lit}`CLRS.Chapter12.BSTree.delete_eq_self_of_not_inTree`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_self_eq_false`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_delete_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_delete_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_delete_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_delete_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.delete_ordered`,
  {lit}`CLRS.Chapter12.BSTree.searchZipper_toTree`,
  {lit}`CLRS.Chapter12.BSTree.searchIter_eq_search`,
  {lit}`CLRS.Chapter12.BSTree.transplant_preserves_ordered`,
  {lit}`CLRS.Chapter12.BSTree.deleteViaTransplant_eq_delete`,
  {lit}`CLRS.Chapter12.BSTree.successorZipper_eq_successor?`,
  {lit}`CLRS.Chapter12.BSTree.predecessorZipper_eq_predecessor?`,
  {lit}`CLRS.Chapter12.BSTree.RepresentsW.tree_unique`,
  {lit}`CLRS.Chapter12.BSTree.transplantChild_left_representsW`,
  {lit}`CLRS.Chapter12.BSTree.transplantChild_right_representsW`, and
  {lit}`CLRS.Chapter12.BSTree.insertPointer_right_representsW`.

## Current Gaps

The zipper layer formalizes parent-oriented navigation and subtree replacement
without changing the inductive tree representation.  Building on it, an
imperative pointer-heap layer models nodes as records with mutable
{lit}`left`/{lit}`right`/{lit}`parent` cells over a {lit}`Std.HashMap` store, and
proves that in-place {lit}`TRANSPLANT` and leaf {lit}`TREE-INSERT` refine the
functional subtree-replacement specification through the {lit}`RepresentsW`
heap-to-tree abstraction.  What remains is an explicit RAM-cost model connecting
these pointer operations to concrete running times.
-/

namespace CLRS
namespace Chapter12
end Chapter12
end CLRS
