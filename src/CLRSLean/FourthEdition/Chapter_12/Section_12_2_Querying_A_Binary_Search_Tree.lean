import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# 12.2. Querying a Binary Search Tree

This fourth-edition reader facade collects the query operations proved in the
shared binary-search-tree development.

## Main results

* {name}`CLRS.Chapter12.BSTree.search_eq_true_iff` proves recursive search correct on
  ordered trees.
* {name}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered` and
  {name}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered` certify the extremal queries.
* {name}`CLRS.Chapter12.BSTree.successor?_least_greater` and
  {name}`CLRS.Chapter12.BSTree.predecessor?_greatest_less` prove the least-greater and
  greatest-less specifications.
* {name}`CLRS.Chapter12.BSTree.searchIter_eq_search`,
  {name}`CLRS.Chapter12.BSTree.successorZipper_eq_successor?`, and
  {name}`CLRS.Chapter12.BSTree.predecessorZipper_eq_predecessor?` connect the
  zipper-based parent-pointer queries to their functional specifications.

The costed variants of search, minimum, maximum, successor, and predecessor
are each bounded by the tree height.  Status: `proved` for this model.
-/
