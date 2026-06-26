import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion

/-!
# Chapter 18 - B-Trees

Chapter 18 starts with a first-pass mathematical B-tree model.  The current
Lean surface fixes key membership, search correctness, direct base search
success/failure wrappers, the CLRS minimum-key height expression,
base/positivity facts, height-step recurrence, height monotonicity, and
specification-level split/insert/delete wrappers with split membership/search
preservation plus direct split old-key corollaries, direct split validity,
successful and unsuccessful search-after-update
specifications, membership-driven search-after-update wrappers, and direct
inserted/deleted-key plus old-key query preservation corollaries, direct
validity short-name wrappers, equality-key update-query wrappers, Prop-level
deletion success specifications, old failed-search preservation wrappers,
together with exact failed membership
specifications and direct failed-membership
preservation wrappers after split, insert, and delete.

## Sections

* 18.1 B-tree model: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter18.BTree.search_correct`,
  {lit}`CLRS.Chapter18.BTree.search_true_iff`,
  {lit}`CLRS.Chapter18.BTree.search_true_of_mem`,
  {lit}`CLRS.Chapter18.BTree.mem_of_search_true`,
  {lit}`CLRS.Chapter18.BTree.search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.search_false_of_not_mem`,
  {lit}`CLRS.Chapter18.BTree.not_mem_of_search_false`,
  {lit}`CLRS.Chapter18.BTree.minKeys_zero`,
  {lit}`CLRS.Chapter18.BTree.minKeys_pos`,
  {lit}`CLRS.Chapter18.BTree.one_le_minKeys`,
  {lit}`CLRS.Chapter18.BTree.minKeys_lower_bound`,
  {lit}`CLRS.Chapter18.BTree.minKeys_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_le_succ`, and
  {lit}`CLRS.Chapter18.BTree.minKeys_monotone_height`.
* 18.2 B-tree insertion: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter18.BTree.splitChild_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.splitChild_valid`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_not_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_not_mem_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_of_mem`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_false_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_false_of_not_mem`,
  {lit}`CLRS.Chapter18.BTree.insert_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.insert_valid`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_search_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_self`,
  {lit}`CLRS.Chapter18.BTree.insert_search_self`,
  {lit}`CLRS.Chapter18.BTree.insert_search_of_eq`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_old`,
  {lit}`CLRS.Chapter18.BTree.insert_search_old`,
  {lit}`CLRS.Chapter18.BTree.insert_search_of_mem`,
  {lit}`CLRS.Chapter18.BTree.insert_not_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_not_mem_of_ne`,
  {lit}`CLRS.Chapter18.BTree.insert_search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_search_false_of_ne`, and
  {lit}`CLRS.Chapter18.BTree.insert_search_false_of_not_mem_ne`.
* 18.3 B-tree deletion: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter18.BTree.delete_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.delete_valid`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_iff_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_search_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_search_iff_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem`,
  {lit}`CLRS.Chapter18.BTree.delete_search_deleted_false`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_of_eq`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_of_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_of_ne_prop`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_ne_prop`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_mem_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_mem_ne_prop`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem_old`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem_of_eq`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_old`, and
  {lit}`CLRS.Chapter18.BTree.delete_search_false_of_not_mem`.

## Current Gaps

Full node occupancy, separator ordering, same-depth leaves, in-node splitting,
node-level deletion repair, and disk-page semantics remain strengthening
targets.
-/

namespace CLRS
namespace Chapter18
end Chapter18
end CLRS
