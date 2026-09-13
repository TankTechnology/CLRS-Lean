import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# 12.3. Insertion and Deletion

This fourth-edition reader facade presents the update theorems proved in the
shared binary-search-tree development.

## Main results

* {name}`CLRS.Chapter12.BSTree.inTree_insert_iff` and
  {name}`CLRS.Chapter12.BSTree.insert_ordered` prove insertion membership and invariant
  preservation.
* {name}`CLRS.Chapter12.BSTree.inTree_delete_iff` and
  {name}`CLRS.Chapter12.BSTree.delete_ordered` prove deletion membership and invariant
  preservation.
* {name}`CLRS.Chapter12.BSTree.transplant_preserves_ordered` and
  {name}`CLRS.Chapter12.BSTree.deleteViaTransplant_eq_delete` connect the textbook
  TRANSPLANT-based deletion to the functional operation.
* The pointer-heap refinement theorems for TRANSPLANT and leaf attachment
  preserve the represented functional tree.

Insertion costs at most {lit}`height + 1` modeled steps, and deletion costs at
most {lit}`2 * height + 3`.  Status: `proved` for the functional and stated
pointer-refinement layers.
-/
