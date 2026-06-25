import CLRSLean.Chapter_20.Section_20_1_VEB_Universe
import CLRSLean.Chapter_20.Section_20_2_VEB_Tree

/-!
# Chapter 20 - van Emde Boas Trees

Chapter 20 starts with a first-pass van Emde Boas universe decomposition and a
finite-set specification model.  The current Lean surface proves high/low/index
arithmetic, including bounded high/low recomposition facts, and the correctness
of membership, extrema, successor, predecessor, insert, and delete against a
represented finite set, including empty-result specifications for extrema,
successor, and predecessor plus membership-, extrema-, and
neighbor-query-after-update positive and no-neighbor specifications,
successful-query universe-bound corollaries, direct extrema
membership/lower- and upper-bound wrappers, direct base/insert/delete neighbor
membership/order wrappers, extrema empty-after-update specifications,
update-query universe-bound corollaries, direct
inserted/deleted key and old-key member-preservation corollaries, exact
failed member-query specifications after updates, and operation-depth
base/step/linear and monotonicity wrappers.

## Sections

* 20.1 Universe decomposition: {lit}`proved` for the first-pass side-length
  arithmetic.
  Main results:
  {lit}`CLRS.Chapter20.VEB.index_high_low`,
  {lit}`CLRS.Chapter20.VEB.high_index`,
  {lit}`CLRS.Chapter20.VEB.low_index`,
  {lit}`CLRS.Chapter20.VEB.index_lt`,
  {lit}`CLRS.Chapter20.VEB.high_lt`, and
  {lit}`CLRS.Chapter20.VEB.low_lt`.
* 20.2 Tree specification: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter20.VEB.member_correct`,
  {lit}`CLRS.Chapter20.VEB.member_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.minimum_mem`,
  {lit}`CLRS.Chapter20.VEB.minimum_le`,
  {lit}`CLRS.Chapter20.VEB.minimum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.maximum_mem`,
  {lit}`CLRS.Chapter20.VEB.le_maximum`,
  {lit}`CLRS.Chapter20.VEB.maximum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.successor_correct`,
  {lit}`CLRS.Chapter20.VEB.successor_mem`,
  {lit}`CLRS.Chapter20.VEB.successor_gt`,
  {lit}`CLRS.Chapter20.VEB.successor_le`,
  {lit}`CLRS.Chapter20.VEB.successor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.predecessor_mem`,
  {lit}`CLRS.Chapter20.VEB.predecessor_lt`,
  {lit}`CLRS.Chapter20.VEB.le_predecessor`,
  {lit}`CLRS.Chapter20.VEB.predecessor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_member_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_member_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_member_self`,
  {lit}`CLRS.Chapter20.VEB.insert_member_old`,
  {lit}`CLRS.Chapter20.VEB.insert_member_false_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_mem`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_gt`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_le`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_mem`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_lt`,
  {lit}`CLRS.Chapter20.VEB.insert_le_predecessor`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_member_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_member_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_member_deleted_false`,
  {lit}`CLRS.Chapter20.VEB.delete_member_of_ne`,
  {lit}`CLRS.Chapter20.VEB.delete_member_false_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_mem`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_gt`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_le`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_mem`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_lt`,
  {lit}`CLRS.Chapter20.VEB.delete_le_predecessor`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_zero`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_succ`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_linear`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_monotone`, and
  {lit}`CLRS.Chapter20.VEB.operationDepth_strict_mono`.

## Current Gaps

Recursive summary/cluster storage, word-RAM base cases, and a Chapter 3
asymptotic bridge for {lit}`O(log log u)` remain strengthening targets.
-/

namespace CLRS
namespace Chapter20
end Chapter20
end CLRS
