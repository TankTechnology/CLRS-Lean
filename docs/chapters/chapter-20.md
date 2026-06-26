# Chapter 20 - van Emde Boas Trees

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_20.lean`
- Interface test: `Tests/Chapter_20_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter20.VEB.index_high_low`
- `CLRS.Chapter20.VEB.high_index`
- `CLRS.Chapter20.VEB.low_index`
- `CLRS.Chapter20.VEB.index_lt`
- `CLRS.Chapter20.VEB.high_lt`
- `CLRS.Chapter20.VEB.low_lt`
- `CLRS.Chapter20.VEB.member_correct`
- `CLRS.Chapter20.VEB.member_lt_univ`
- `CLRS.Chapter20.VEB.minimum_correct`
- `CLRS.Chapter20.VEB.minimum_mem`
- `CLRS.Chapter20.VEB.minimum_le`
- `CLRS.Chapter20.VEB.minimum_lt_univ`
- `CLRS.Chapter20.VEB.minimum_none_iff`
- `CLRS.Chapter20.VEB.minimum_none_of_empty`
- `CLRS.Chapter20.VEB.minimum_ne_none_of_nonempty`
- `CLRS.Chapter20.VEB.maximum_correct`
- `CLRS.Chapter20.VEB.maximum_mem`
- `CLRS.Chapter20.VEB.le_maximum`
- `CLRS.Chapter20.VEB.maximum_lt_univ`
- `CLRS.Chapter20.VEB.maximum_none_iff`
- `CLRS.Chapter20.VEB.maximum_none_of_empty`
- `CLRS.Chapter20.VEB.maximum_ne_none_of_nonempty`
- `CLRS.Chapter20.VEB.successor_correct`
- `CLRS.Chapter20.VEB.successor_mem`
- `CLRS.Chapter20.VEB.successor_gt`
- `CLRS.Chapter20.VEB.successor_le`
- `CLRS.Chapter20.VEB.successor_lt_univ`
- `CLRS.Chapter20.VEB.successor_none_iff`
- `CLRS.Chapter20.VEB.successor_none_of_no_gt`
- `CLRS.Chapter20.VEB.successor_ne_none_of_exists_gt`
- `CLRS.Chapter20.VEB.predecessor_correct`
- `CLRS.Chapter20.VEB.predecessor_mem`
- `CLRS.Chapter20.VEB.predecessor_lt`
- `CLRS.Chapter20.VEB.le_predecessor`
- `CLRS.Chapter20.VEB.predecessor_lt_univ`
- `CLRS.Chapter20.VEB.predecessor_none_iff`
- `CLRS.Chapter20.VEB.predecessor_none_of_no_lt`
- `CLRS.Chapter20.VEB.predecessor_ne_none_of_exists_lt`
- `CLRS.Chapter20.VEB.insert_correct`
- `CLRS.Chapter20.VEB.insert_member_iff`
- `CLRS.Chapter20.VEB.insert_member_lt_univ`
- `CLRS.Chapter20.VEB.insert_member_self`
- `CLRS.Chapter20.VEB.insert_member_old`
- `CLRS.Chapter20.VEB.insert_member_false_iff`
- `CLRS.Chapter20.VEB.insert_member_false_of_ne`
- `CLRS.Chapter20.VEB.insert_minimum_correct`
- `CLRS.Chapter20.VEB.insert_minimum_mem`
- `CLRS.Chapter20.VEB.insert_minimum_mem_old_of_ne`
- `CLRS.Chapter20.VEB.insert_minimum_le_inserted`
- `CLRS.Chapter20.VEB.insert_minimum_le_old`
- `CLRS.Chapter20.VEB.insert_minimum_lt_univ`
- `CLRS.Chapter20.VEB.insert_minimum_none_iff`
- `CLRS.Chapter20.VEB.insert_minimum_ne_none`
- `CLRS.Chapter20.VEB.insert_maximum_correct`
- `CLRS.Chapter20.VEB.insert_maximum_mem`
- `CLRS.Chapter20.VEB.insert_maximum_mem_old_of_ne`
- `CLRS.Chapter20.VEB.insert_maximum_inserted_le`
- `CLRS.Chapter20.VEB.insert_maximum_old_le`
- `CLRS.Chapter20.VEB.insert_maximum_lt_univ`
- `CLRS.Chapter20.VEB.insert_maximum_none_iff`
- `CLRS.Chapter20.VEB.insert_maximum_ne_none`
- `CLRS.Chapter20.VEB.insert_successor_correct`
- `CLRS.Chapter20.VEB.insert_successor_mem`
- `CLRS.Chapter20.VEB.insert_successor_mem_old_of_ne`
- `CLRS.Chapter20.VEB.insert_successor_gt`
- `CLRS.Chapter20.VEB.insert_successor_le`
- `CLRS.Chapter20.VEB.insert_successor_lt_univ`
- `CLRS.Chapter20.VEB.insert_successor_none_iff`
- `CLRS.Chapter20.VEB.insert_successor_none_of_no_gt`
- `CLRS.Chapter20.VEB.insert_successor_none_of_insert_le_old_no_gt`
- `CLRS.Chapter20.VEB.insert_successor_ne_none_of_insert_gt`
- `CLRS.Chapter20.VEB.insert_successor_ne_none_of_old_gt`
- `CLRS.Chapter20.VEB.insert_predecessor_correct`
- `CLRS.Chapter20.VEB.insert_predecessor_mem`
- `CLRS.Chapter20.VEB.insert_predecessor_mem_old_of_ne`
- `CLRS.Chapter20.VEB.insert_predecessor_lt`
- `CLRS.Chapter20.VEB.insert_le_predecessor`
- `CLRS.Chapter20.VEB.insert_predecessor_lt_univ`
- `CLRS.Chapter20.VEB.insert_predecessor_none_iff`
- `CLRS.Chapter20.VEB.insert_predecessor_none_of_no_lt`
- `CLRS.Chapter20.VEB.insert_predecessor_none_of_query_le_insert_old_no_lt`
- `CLRS.Chapter20.VEB.insert_predecessor_ne_none_of_insert_lt`
- `CLRS.Chapter20.VEB.insert_predecessor_ne_none_of_old_lt`
- `CLRS.Chapter20.VEB.delete_correct`
- `CLRS.Chapter20.VEB.delete_member_iff`
- `CLRS.Chapter20.VEB.delete_member_lt_univ`
- `CLRS.Chapter20.VEB.delete_member_deleted_false`
- `CLRS.Chapter20.VEB.delete_member_of_ne`
- `CLRS.Chapter20.VEB.delete_member_false_iff`
- `CLRS.Chapter20.VEB.delete_member_false_old`
- `CLRS.Chapter20.VEB.delete_member_false_of_eq`
- `CLRS.Chapter20.VEB.delete_minimum_correct`
- `CLRS.Chapter20.VEB.delete_minimum_ne`
- `CLRS.Chapter20.VEB.delete_minimum_mem`
- `CLRS.Chapter20.VEB.delete_minimum_le_old`
- `CLRS.Chapter20.VEB.delete_minimum_lt_univ`
- `CLRS.Chapter20.VEB.delete_minimum_none_iff`
- `CLRS.Chapter20.VEB.delete_minimum_none_of_all_eq`
- `CLRS.Chapter20.VEB.delete_minimum_ne_none_of_remaining`
- `CLRS.Chapter20.VEB.delete_maximum_correct`
- `CLRS.Chapter20.VEB.delete_maximum_ne`
- `CLRS.Chapter20.VEB.delete_maximum_mem`
- `CLRS.Chapter20.VEB.delete_maximum_old_le`
- `CLRS.Chapter20.VEB.delete_maximum_lt_univ`
- `CLRS.Chapter20.VEB.delete_maximum_none_iff`
- `CLRS.Chapter20.VEB.delete_maximum_none_of_all_eq`
- `CLRS.Chapter20.VEB.delete_maximum_ne_none_of_remaining`
- `CLRS.Chapter20.VEB.delete_successor_correct`
- `CLRS.Chapter20.VEB.delete_successor_mem`
- `CLRS.Chapter20.VEB.delete_successor_gt`
- `CLRS.Chapter20.VEB.delete_successor_le`
- `CLRS.Chapter20.VEB.delete_successor_lt_univ`
- `CLRS.Chapter20.VEB.delete_successor_none_iff`
- `CLRS.Chapter20.VEB.delete_successor_none_of_no_gt`
- `CLRS.Chapter20.VEB.delete_successor_none_of_old_no_gt`
- `CLRS.Chapter20.VEB.delete_successor_ne_none_of_remaining_gt`
- `CLRS.Chapter20.VEB.delete_predecessor_correct`
- `CLRS.Chapter20.VEB.delete_predecessor_mem`
- `CLRS.Chapter20.VEB.delete_predecessor_lt`
- `CLRS.Chapter20.VEB.delete_le_predecessor`
- `CLRS.Chapter20.VEB.delete_predecessor_lt_univ`
- `CLRS.Chapter20.VEB.delete_predecessor_none_iff`
- `CLRS.Chapter20.VEB.delete_predecessor_none_of_no_lt`
- `CLRS.Chapter20.VEB.delete_predecessor_none_of_old_no_lt`
- `CLRS.Chapter20.VEB.delete_predecessor_ne_none_of_remaining_lt`
- `CLRS.Chapter20.VEB.operationDepth_zero`
- `CLRS.Chapter20.VEB.operationDepth_succ`
- `CLRS.Chapter20.VEB.operationDepth_linear`
- `CLRS.Chapter20.VEB.operationDepth_monotone`
- `CLRS.Chapter20.VEB.operationDepth_strict_mono`

## Remaining Work

The current chapter proves side-length universe arithmetic, including bounded
high/low recomposition facts, and finite-set operation specifications.
It also records direct member-query corollaries for inserted/deleted keys,
old-key preservation, and exact failed member queries after updates,
direct failed member-query preservation wrappers, successful-query
universe-bound corollaries, direct extrema membership/lower- and upper-bound
wrappers, direct extrema-after-update membership/order wrappers, direct
base/insert/delete neighbor membership/order wrappers, positive and
empty-result extrema-after-update
specs, positive and no-neighbor update-query specs, update-query
universe-bound corollaries, direct no-neighbor query wrappers, premise-light
no-neighbor wrappers over old represented sets, direct extrema empty-result
wrappers, direct base extrema/neighbor nonempty-result wrappers, direct
updated-neighbor nonempty-result wrappers, direct deletion-extrema
nonempty-result wrappers, plus the
first-pass operation-depth base, step, linear, and
monotonicity facts.
Recursive summary/cluster state, word-RAM base cases, and a full `O(log log u)`
asymptotic bridge are still open.
