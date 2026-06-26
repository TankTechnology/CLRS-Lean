# Chapter 18 - B-Trees

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_18.lean`
- Interface test: `Tests/Chapter_18_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter18.BTree.search_correct`
- `CLRS.Chapter18.BTree.search_true_iff`
- `CLRS.Chapter18.BTree.search_true_of_mem`
- `CLRS.Chapter18.BTree.mem_of_search_true`
- `CLRS.Chapter18.BTree.search_false_iff`
- `CLRS.Chapter18.BTree.search_false_of_not_mem`
- `CLRS.Chapter18.BTree.not_mem_of_search_false`
- `CLRS.Chapter18.BTree.minKeys_zero`
- `CLRS.Chapter18.BTree.minKeys_pos`
- `CLRS.Chapter18.BTree.one_le_minKeys`
- `CLRS.Chapter18.BTree.minKeys_lower_bound`
- `CLRS.Chapter18.BTree.minKeys_succ`
- `CLRS.Chapter18.BTree.minKeys_le_succ`
- `CLRS.Chapter18.BTree.minKeys_monotone_height`
- `CLRS.Chapter18.BTree.splitChild_preserves_model`
- `CLRS.Chapter18.BTree.splitChild_valid`
- `CLRS.Chapter18.BTree.splitChild_mem_iff`
- `CLRS.Chapter18.BTree.splitChild_mem_old`
- `CLRS.Chapter18.BTree.splitChild_not_mem_iff`
- `CLRS.Chapter18.BTree.splitChild_not_mem_old`
- `CLRS.Chapter18.BTree.splitChild_search_iff`
- `CLRS.Chapter18.BTree.splitChild_search_old`
- `CLRS.Chapter18.BTree.splitChild_search_of_mem`
- `CLRS.Chapter18.BTree.splitChild_search_false_iff`
- `CLRS.Chapter18.BTree.splitChild_search_false_old`
- `CLRS.Chapter18.BTree.splitChild_search_false_of_not_mem`
- `CLRS.Chapter18.BTree.insert_preserves_model`
- `CLRS.Chapter18.BTree.insert_valid`
- `CLRS.Chapter18.BTree.insert_mem_iff`
- `CLRS.Chapter18.BTree.insert_search_iff`
- `CLRS.Chapter18.BTree.insert_mem_self`
- `CLRS.Chapter18.BTree.insert_search_self`
- `CLRS.Chapter18.BTree.insert_search_of_eq`
- `CLRS.Chapter18.BTree.insert_mem_old`
- `CLRS.Chapter18.BTree.insert_search_old`
- `CLRS.Chapter18.BTree.insert_search_of_mem`
- `CLRS.Chapter18.BTree.insert_not_mem_iff`
- `CLRS.Chapter18.BTree.insert_not_mem_of_ne`
- `CLRS.Chapter18.BTree.insert_search_false_iff`
- `CLRS.Chapter18.BTree.insert_search_false_of_ne`
- `CLRS.Chapter18.BTree.insert_search_false_of_not_mem_ne`
- `CLRS.Chapter18.BTree.delete_preserves_model`
- `CLRS.Chapter18.BTree.delete_valid`
- `CLRS.Chapter18.BTree.delete_mem_iff`
- `CLRS.Chapter18.BTree.delete_mem_iff_ne`
- `CLRS.Chapter18.BTree.delete_search_iff`
- `CLRS.Chapter18.BTree.delete_search_iff_ne`
- `CLRS.Chapter18.BTree.delete_not_mem`
- `CLRS.Chapter18.BTree.delete_search_deleted_false`
- `CLRS.Chapter18.BTree.delete_search_false_of_eq`
- `CLRS.Chapter18.BTree.delete_mem_of_ne`
- `CLRS.Chapter18.BTree.delete_mem_of_ne_prop`
- `CLRS.Chapter18.BTree.delete_search_of_ne`
- `CLRS.Chapter18.BTree.delete_search_of_ne_prop`
- `CLRS.Chapter18.BTree.delete_search_of_mem_ne`
- `CLRS.Chapter18.BTree.delete_search_of_mem_ne_prop`
- `CLRS.Chapter18.BTree.delete_not_mem_iff`
- `CLRS.Chapter18.BTree.delete_not_mem_old`
- `CLRS.Chapter18.BTree.delete_not_mem_of_eq`
- `CLRS.Chapter18.BTree.delete_search_false_iff`
- `CLRS.Chapter18.BTree.delete_search_false_old`
- `CLRS.Chapter18.BTree.delete_search_false_of_not_mem`

## Remaining Work

The current chapter uses a mathematical key-membership model, a minimum-key
height-expression base/positivity facts, recurrence, and monotonicity facts,
direct base search success/failure wrappers, and specification wrappers for
split/insert/delete, including direct split validity/preservation corollaries
and direct successful/unsuccessful query corollaries for the inserted and
deleted keys plus old-key preservation, insertion/deletion validity short-name
wrappers, equality-key update-query wrappers, membership-driven
search-after-update wrappers, and old failed-search preservation, plus
exact failed membership specifications and direct failed-membership preservation
wrappers.
Full separator ordering, same-depth leaves, node-level deletion repair,
disk-page I/O, and pointer-level mutation remain future refinements.
