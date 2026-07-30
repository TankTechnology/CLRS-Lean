# Chapter 18 - B-Trees

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_18.lean`
- Interface tests: `Tests/Chapter_18_Search_Interface.lean`,
  `Tests/Chapter_18_Interface.lean`,
  `Tests/Chapter_18_Deletion_Interface.lean`

## Search Surfaces

`CLRS.Chapter18.BTree.search` remains the specification oracle used for
compatibility with the original model: it decides whether a key belongs to the
flattened key collection.  `CLRS.Chapter18.BTree.searchExec` is the executable
CLRS-style search: it checks the current node and otherwise recurses only into
the child chosen by the separators.

For sorted, child-bounded trees,
`CLRS.Chapter18.BTree.searchExec_true_iff` is the semantic truth source for the
executable algorithm.  Its two directions are also available separately as
`CLRS.Chapter18.BTree.searchExec_sound`, which needs no structural invariant,
and `CLRS.Chapter18.BTree.searchExec_complete`.
`CLRS.Chapter18.BTree.searchExec_eq_search` records compatibility with the
specification oracle.

On a sorted, child-bounded node,
`CLRS.Chapter18.BTree.findChild_localizes_mem` proves that when a key is not a
separator of the current node, any child containing it has exactly the index
selected by `findChild`.  This theorem supplies the path-localization step
needed by the still-open exact-semantics proof for executable deletion; it does
not by itself establish that deletion refinement.

## Proved Public Surface

- `CLRS.Chapter18.BTree.search_correct`
- `CLRS.Chapter18.BTree.search_true_iff`
- `CLRS.Chapter18.BTree.search_true_of_mem`
- `CLRS.Chapter18.BTree.mem_of_search_true`
- `CLRS.Chapter18.BTree.search_false_iff`
- `CLRS.Chapter18.BTree.search_false_of_not_mem`
- `CLRS.Chapter18.BTree.not_mem_of_search_false`
- `CLRS.Chapter18.BTree.findChild`
- `CLRS.Chapter18.BTree.findChild_localizes_mem`
- `CLRS.Chapter18.BTree.searchExec`
- `CLRS.Chapter18.BTree.searchExec_sound`
- `CLRS.Chapter18.BTree.searchExec_complete`
- `CLRS.Chapter18.BTree.searchExec_true_iff`
- `CLRS.Chapter18.BTree.searchExec_eq_search`
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

## Structural Deletion Results

The executable `composedDelete` proof is bundled rather than duplicated across
the individual invariants:

- `CLRS.Chapter18.BTree.composedDelete_packet`
- `CLRS.Chapter18.BTree.composedDelete_nonRoot_preserves`
- `CLRS.Chapter18.BTree.composedDelete_rootResult`
- `CLRS.Chapter18.BTree.keysOf_composedDelete_subset`
- `CLRS.Chapter18.BTree.composedDelete_key_bound_lo`
- `CLRS.Chapter18.BTree.composedDelete_key_bound_hi`
- `CLRS.Chapter18.BTree.composedDelete_sameDepth_height`
- `CLRS.Chapter18.BTree.composedDelete_sorted`
- `CLRS.Chapter18.BTree.composedDelete_childBounded`
- `CLRS.Chapter18.BTree.composedDelete_occupancy`
- `CLRS.Chapter18.BTree.normalizeRoot_wellFormed`
- `CLRS.Chapter18.BTree.composedDeleteRoot_keys_subset`
- `CLRS.Chapter18.BTree.composedDeleteRoot_height`
- `CLRS.Chapter18.BTree.composedDeleteRoot_wellFormed`

The 19 former component proof gaps are eliminated.  Conclusions that require
the full invariant packet project from the bundled preservation result, while
`composedDelete_sameDepth_height` keeps its weaker
`ChildBounded + SameDepth` contract through a dedicated structural induction.

Raw root deletion deliberately has the weaker `RootDeleteResult` postcondition:
it may return an empty root with one child.  `composedDeleteRoot` applies
`normalizeRoot`, after which `WellFormed` holds, all result keys come from the
input, and the height is unchanged or decreases by exactly one.

## Remaining Work

The main missing theorem connects the executable root operation to exact
multiset semantics: prove a `keysOf` equation identifying
`keysOf (composedDeleteRoot t x tr)` with the input `keysOf` multiset after
erasing one occurrence of `x`.  Preservation of every key different from `x`
then follows unconditionally.  Because the current model permits duplicate
keys, complete absence of `x` is not an unconditional consequence; that
corollary requires a new `UniqueKeys` layer.  The abstract `delete`
specification already exposes its specification-level membership behavior,
but this executable refinement and the `UniqueKeys` layer are not yet proved,
so Chapter 18 remains `partial`.  The selected-child localization theorem now
provides the search-path lemma for that future proof, but no exact multiset
theorem for `composedDeleteRoot` is claimed yet.

Disk-page layout, pointer mutation, page I/O counts, and RAM-cost semantics are
optional lower-level refinements rather than blockers for the mathematical
deletion theorem.
