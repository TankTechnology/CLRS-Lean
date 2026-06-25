import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion

/-!
# Chapter 18 - B-Trees

Chapter 18 starts with a first-pass mathematical B-tree model.  The current
Lean surface fixes key membership, search correctness, the CLRS minimum-key
height expression and height-step recurrence, and specification-level
split/insert/delete wrappers with split membership/search preservation and
search-after-update specifications.

## Sections

* 18.1 B-tree model: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter18.BTree.search_correct` and
  {lit}`CLRS.Chapter18.BTree.minKeys_lower_bound`, and
  {lit}`CLRS.Chapter18.BTree.minKeys_succ`.
* 18.2 B-tree insertion: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter18.BTree.splitChild_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_iff`, and
  {lit}`CLRS.Chapter18.BTree.insert_search_iff`.
* 18.3 B-tree deletion: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter18.BTree.delete_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_iff`, and
  {lit}`CLRS.Chapter18.BTree.delete_search_iff`.

## Current Gaps

Full node occupancy, separator ordering, same-depth leaves, in-node splitting,
node-level deletion repair, and disk-page semantics remain strengthening
targets.
-/

namespace CLRS
namespace Chapter18
end Chapter18
end CLRS
