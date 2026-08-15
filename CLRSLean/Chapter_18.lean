import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.Search
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.HeightBound
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.RunningTime
import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Invariant
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Rotation
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Repair
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Preservation
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Reassembly
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.MergeReassembly
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.RotationBounds
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.RotationReassembly
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Subset
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.SameDepthHeight
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Sorted
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ChildBounded
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Occupancy
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.WellFormed

/-!
# Chapter 18 - B-Trees

Chapter 18 starts with a first-pass mathematical B-tree model.  Its
specification-level {lit}`search` operation remains a compatibility oracle
defined from membership, while {lit}`searchExec` is the separator-guided
executable algorithm.  On sorted, child-bounded trees,
{lit}`searchExec_true_iff` is the semantic truth source connecting that
algorithm to membership; {lit}`searchExec_sound` and
{lit}`searchExec_complete` expose the two directions separately.
{lit}`findChild_localizes_mem` proves that, in a sorted, child-bounded node, a
non-separator member lies in the selected child.  This localization result is
used by the exact semantics proof for executable deletion, together with
direct selected-child and predecessor-routing wrappers.

The current Lean surface additionally fixes direct base-search success/failure
wrappers, the CLRS minimum-key height expression,
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

Section 18.1 now also connects the structural invariants to the textbook
height analysis.  {lit}`totalKeys` counts represented key slots without a
uniqueness premise; the root lower bound explicitly separates the legal empty
tree, while for {lit}`2 ≤ t`, {lit}`wellFormed_height_log_bound` applies to
every {lit}`WellFormed` tree and packages the CLRS logarithmic-height theorem.

Section 18.2 retains the flat {lit}`insert` as its specification layer and now
proves the real top-level CLRS insertion operation {lit}`insertRoot`.
{lit}`splitRoot` installs a full old root below a transient empty parent and
applies the full-child split; the transient parent itself is not claimed
{lit}`WellFormed`, but the split output is.  Top-level insertion adds exactly
one key, preserves {lit}`WellFormed`, has an exact same-or-one-higher
conditional height theorem, agrees with the specification on membership and
membership-oracle search, and supports correct executable search.  This is an
extensional compatibility result, not executable/specification tree-shape
equality.  Preservation of {lit}`WellFormedUnique` additionally requires that
the inserted key was absent.

Section 18.3 also contains the executable node-level deletion proof.  A single
bundled induction proves key containment and the complete structural invariant
packet across leaf deletion, separator replacement, rotations, and merges.
Raw root deletion may produce an empty root with one child; the public
{lit}`composedDeleteRoot` operation contracts that transient before exposing
root-level well-formedness.  Its key multiset is the input multiset after
{lit}`Multiset.erase` removes one requested-key occurrence when present,
assuming only the structural invariant and {lit}`2 ≤ t`; membership of every
different key is therefore preserved without uniqueness.  Under
{lit}`WellFormedUnique`, deletion also removes the requested key completely
and agrees with the specification-level
{lit}`delete` operation on membership and compatibility-oracle search.  This
is a semantic refinement, not a claim that the two operations return the same
tree shape.

## Sections

* 18.1 B-tree model, search, and height bound: proved for the current
  functional correctness model.
  Main results:
  {lit}`CLRS.Chapter18.BTree.search_correct`,
  {lit}`CLRS.Chapter18.BTree.search_true_iff`,
  {lit}`CLRS.Chapter18.BTree.search_true_of_mem`,
  {lit}`CLRS.Chapter18.BTree.mem_of_search_true`,
  {lit}`CLRS.Chapter18.BTree.search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.search_false_of_not_mem`,
  {lit}`CLRS.Chapter18.BTree.not_mem_of_search_false`,
  {lit}`CLRS.Chapter18.BTree.findChild`,
  {lit}`CLRS.Chapter18.BTree.findChild_localizes_mem`,
  {lit}`CLRS.Chapter18.BTree.searchExec`,
  {lit}`CLRS.Chapter18.BTree.searchExec_sound`,
  {lit}`CLRS.Chapter18.BTree.searchExec_complete`,
  {lit}`CLRS.Chapter18.BTree.searchExec_true_iff`,
  {lit}`CLRS.Chapter18.BTree.searchExec_eq_search`,
  {lit}`CLRS.Chapter18.BTree.minKeys_zero`,
  {lit}`CLRS.Chapter18.BTree.minKeys_pos`,
  {lit}`CLRS.Chapter18.BTree.one_le_minKeys`,
  {lit}`CLRS.Chapter18.BTree.minKeys_lower_bound`,
  {lit}`CLRS.Chapter18.BTree.minKeys_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_le_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_monotone_height`,
  {lit}`CLRS.Chapter18.BTree.totalKeys`,
  {lit}`CLRS.Chapter18.BTree.totalKeys_node`,
  {lit}`CLRS.Chapter18.BTree.nonRoot_totalKeys_add_one_lower_bound`,
  {lit}`CLRS.Chapter18.BTree.wellFormed_empty_or_totalKeys_add_one_lower_bound`,
  {lit}`CLRS.Chapter18.BTree.wellFormed_empty_or_minKeys_le_totalKeys`,
  {lit}`CLRS.Chapter18.BTree.wellFormed_minKeys_le_totalKeys`, and
  {lit}`CLRS.Chapter18.BTree.wellFormed_height_log_bound`.
* 18.2 B-tree insertion: proved for the current functional correctness model.
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
  {lit}`CLRS.Chapter18.BTree.insert_search_false_of_ne`,
  {lit}`CLRS.Chapter18.BTree.insert_search_false_of_not_mem_ne`,
  {lit}`CLRS.Chapter18.BTree.splitRoot`,
  {lit}`CLRS.Chapter18.BTree.insertRoot`,
  {lit}`CLRS.Chapter18.BTree.splitRoot_keys_perm`,
  {lit}`CLRS.Chapter18.BTree.splitRoot_wellFormed`,
  {lit}`CLRS.Chapter18.BTree.splitRoot_height`,
  {lit}`CLRS.Chapter18.BTree.splitRoot_rootKeyCount`,
  {lit}`CLRS.Chapter18.BTree.splitRoot_nonFull`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_keys_perm`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_wellFormed`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_height`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_wellFormedUnique`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_mem_iff_insert`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_search_eq_insert`,
  {lit}`CLRS.Chapter18.BTree.insertRoot_searchExec_true_iff`, and
  {lit}`CLRS.Chapter18.BTree.insertRoot_correct`.
* 18.3 B-tree deletion: proved for the current functional model.
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
  {lit}`CLRS.Chapter18.BTree.delete_search_false_old`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_of_not_mem`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_packet`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_nonRoot_preserves`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_rootResult`,
  {lit}`CLRS.Chapter18.BTree.keysOf_composedDelete_subset`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_key_bound_lo`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_key_bound_hi`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_sameDepth_height`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_sorted`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_childBounded`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_occupancy`,
  {lit}`CLRS.Chapter18.BTree.normalizeRoot_wellFormed`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_keys_subset`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_height`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_wellFormed`,
  {lit}`CLRS.Chapter18.BTree.UniqueKeys`,
  {lit}`CLRS.Chapter18.BTree.WellFormedUnique`,
  {lit}`CLRS.Chapter18.BTree.findChild_pos_and_pred_eq_of_mem`,
  {lit}`CLRS.Chapter18.BTree.findChild_not_mem_child_of_ne`,
  {lit}`CLRS.Chapter18.BTree.findChild_selected_child_mem`,
  {lit}`CLRS.Chapter18.BTree.keyBag`,
  {lit}`CLRS.Chapter18.BTree.keyBag_erase_of_balance`,
  {lit}`CLRS.Chapter18.BTree.sortedRemove_keyBag`,
  {lit}`CLRS.Chapter18.BTree.mergeNodes_keyBag`,
  {lit}`CLRS.Chapter18.BTree.rotateRight_keyBag`,
  {lit}`CLRS.Chapter18.BTree.rotateLeft_keyBag`,
  {lit}`CLRS.Chapter18.BTree.replaceChild_keyBag_erase`,
  {lit}`CLRS.Chapter18.BTree.replacePredecessor_keyBag_erase`,
  {lit}`CLRS.Chapter18.BTree.replaceSuccessor_keyBag_erase`,
  {lit}`CLRS.Chapter18.BTree.spliceMerged_keyBag_erase`,
  {lit}`CLRS.Chapter18.BTree.rotateRight_reassembly_keyBag_erase`,
  {lit}`CLRS.Chapter18.BTree.rotateLeft_reassembly_keyBag_erase`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_keyBag`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_mem_iff_of_ne`,
  {lit}`CLRS.Chapter18.BTree.composedDelete_uniqueKeys`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_keyBag`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff_of_ne`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_not_mem`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_wellFormedUnique`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff_delete`,
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_search_eq_delete`, and
  {lit}`CLRS.Chapter18.BTree.composedDeleteRoot_correct`.

## Completion Boundary

Search, top-level insertion and structural preservation, exact
{lit}`Multiset.erase` deletion semantics, the structural total-key and
logarithmic-height bounds, and the running-time / cost layer are complete
under the documented assumptions for the current functional B-tree model.
{lit}`searchCost`, {lit}`insertCost`, {lit}`insertRootCost`, and
{lit}`deleteCost` mirror the executable {lit}`searchExec`,
{lit}`insertNonFull`, {lit}`insertRoot`, and {lit}`composedDelete`
constructions, and every one is bounded by {lit}`heightOf + O(1)`; composing
with {lit}`wellFormed_height_log_bound` gives the CLRS
{lit}`O(log_t n)` disk-access bound ({lit}`diskAccessBound`).  Disk-page
layout, pointer mutation, and RAM semantics remain optional lower-level
refinements.
-/

namespace CLRS
namespace Chapter18
end Chapter18
end CLRS
