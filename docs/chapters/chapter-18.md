# Chapter 18 - B-Trees

- Status: `main-proof-complete-for-correctness`
- Lean entry: `CLRSLean/Chapter_18.lean`
- Interface tests: `Tests/Chapter_18_Search_Interface.lean`,
  `Tests/Chapter_18_Insertion_Interface.lean`,
  `Tests/Chapter_18_KeyMultiset_Interface.lean`,
  `Tests/Chapter_18_Deletion_Reassembly_Interface.lean`,
  `Tests/Chapter_18_Deletion_Exact_Interface.lean`,
  `Tests/Chapter_18_Deletion_Root_Exact_Interface.lean`,
  `Tests/Chapter_18_Height_Interface.lean`,
  `Tests/Chapter_18_Interface.lean`,
  `Tests/Chapter_18_Deletion_Interface.lean`,
  `Tests/Chapter_18_Root_Occupancy.lean`

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
selected by `findChild`.  The direct routing wrappers built from this theorem
supply the selected-path facts used by the proved exact-semantics induction
for executable deletion.

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
- `CLRS.Chapter18.BTree.totalKeys`
- `CLRS.Chapter18.BTree.totalKeys_node`
- `CLRS.Chapter18.BTree.nonRoot_totalKeys_add_one_lower_bound`
- `CLRS.Chapter18.BTree.wellFormed_empty_or_totalKeys_add_one_lower_bound`
- `CLRS.Chapter18.BTree.wellFormed_empty_or_minKeys_le_totalKeys`
- `CLRS.Chapter18.BTree.wellFormed_minKeys_le_totalKeys`
- `CLRS.Chapter18.BTree.wellFormed_height_log_bound`
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

## Structural Key-Count and Height Results

Section 18.1 now connects the B-tree invariants to the textbook minimum-key
and logarithmic-height bounds.  `totalKeys` counts key slots in the flattened
`List`, so the structural argument does not assume `UniqueKeys`.
`nonRoot_totalKeys_add_one_lower_bound` proves the augmented power lower bound
for every occupied non-root subtree.  At the root,
`wellFormed_empty_or_totalKeys_add_one_lower_bound` preserves the legal empty
tree as an explicit disjunct and proves the stronger augmented count in the
nonempty branch.

The older `minKeys_lower_bound` is only an expression-level unfolding fact.
The new `wellFormed_empty_or_minKeys_le_totalKeys` and
`wellFormed_minKeys_le_totalKeys` theorems connect that expression to an actual
well-formed tree.  Finally, `wellFormed_height_log_bound` packages the CLRS
base-minimum-degree logarithmic height theorem for every `WellFormed` tree,
including the empty root.

## Top-Level Insertion Results

Section 18.2 is proved for the current functional correctness model.  The
existing flat `CLRS.Chapter18.BTree.insert` remains the specification layer;
the executable top-level CLRS operation is
`CLRS.Chapter18.BTree.insertRoot`.  When the root is full, `splitRoot` installs
it as the sole child of a transient empty parent, applies the full-child split,
and then `insertRoot` calls `insertNonFull`.  The transient parent is not
claimed to satisfy `WellFormed`; `splitRoot_wellFormed` establishes the
invariant only for the completed split result.

The 16 newly tracked public contracts are:

- `CLRS.Chapter18.BTree.splitRoot`
- `CLRS.Chapter18.BTree.insertRoot`
- `CLRS.Chapter18.BTree.splitRoot_keys_perm`
- `CLRS.Chapter18.BTree.splitRoot_wellFormed`
- `CLRS.Chapter18.BTree.splitRoot_height`
- `CLRS.Chapter18.BTree.splitRoot_rootKeyCount`
- `CLRS.Chapter18.BTree.splitRoot_nonFull`
- `CLRS.Chapter18.BTree.insertRoot_keys_perm`
- `CLRS.Chapter18.BTree.insertRoot_wellFormed`
- `CLRS.Chapter18.BTree.insertRoot_height`
- `CLRS.Chapter18.BTree.insertRoot_mem_iff`
- `CLRS.Chapter18.BTree.insertRoot_wellFormedUnique`
- `CLRS.Chapter18.BTree.insertRoot_mem_iff_insert`
- `CLRS.Chapter18.BTree.insertRoot_search_eq_insert`
- `CLRS.Chapter18.BTree.insertRoot_searchExec_true_iff`
- `CLRS.Chapter18.BTree.insertRoot_correct`

`insertRoot_keys_perm` gives the exact content equation as a `List.Perm` of the
old flattened keys followed by `[x]`.  The output is `WellFormed`, and
`insertRoot_height` states the exact conditional: height increases by one
precisely in the full-root branch and is otherwise unchanged.
`insertRoot_mem_iff` says membership is exactly `y = x ∨ mem y tr`;
`insertRoot_mem_iff_insert` and `insertRoot_search_eq_insert` give membership
and membership-oracle search compatibility with the flat specification, while
`insertRoot_searchExec_true_iff` proves executable-search correctness on the
output.  `insertRoot_wellFormedUnique` requires the necessary premise
`¬ mem x tr`.

These compatibility theorems are extensional.  They do not claim equality
between the executable and specification tree shapes.

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

## Exact Deletion Results

The exact deletion layer adds these 28 tracked, reader-facing typed contracts:

- `CLRS.Chapter18.BTree.UniqueKeys`
- `CLRS.Chapter18.BTree.WellFormedUnique`
- `CLRS.Chapter18.BTree.findChild_pos_and_pred_eq_of_mem`
- `CLRS.Chapter18.BTree.findChild_not_mem_child_of_ne`
- `CLRS.Chapter18.BTree.findChild_selected_child_mem`
- `CLRS.Chapter18.BTree.keyBag`
- `CLRS.Chapter18.BTree.keyBag_erase_of_balance`
- `CLRS.Chapter18.BTree.sortedRemove_keyBag`
- `CLRS.Chapter18.BTree.mergeNodes_keyBag`
- `CLRS.Chapter18.BTree.rotateRight_keyBag`
- `CLRS.Chapter18.BTree.rotateLeft_keyBag`
- `CLRS.Chapter18.BTree.replaceChild_keyBag_erase`
- `CLRS.Chapter18.BTree.replacePredecessor_keyBag_erase`
- `CLRS.Chapter18.BTree.replaceSuccessor_keyBag_erase`
- `CLRS.Chapter18.BTree.spliceMerged_keyBag_erase`
- `CLRS.Chapter18.BTree.rotateRight_reassembly_keyBag_erase`
- `CLRS.Chapter18.BTree.rotateLeft_reassembly_keyBag_erase`
- `CLRS.Chapter18.BTree.composedDelete_keyBag`
- `CLRS.Chapter18.BTree.composedDelete_mem_iff_of_ne`
- `CLRS.Chapter18.BTree.composedDelete_uniqueKeys`
- `CLRS.Chapter18.BTree.composedDeleteRoot_keyBag`
- `CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff_of_ne`
- `CLRS.Chapter18.BTree.composedDeleteRoot_not_mem`
- `CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff`
- `CLRS.Chapter18.BTree.composedDeleteRoot_wellFormedUnique`
- `CLRS.Chapter18.BTree.composedDeleteRoot_mem_iff_delete`
- `CLRS.Chapter18.BTree.composedDeleteRoot_search_eq_delete`
- `CLRS.Chapter18.BTree.composedDeleteRoot_correct`

For `2 ≤ t`, `composedDelete_keyBag` needs only `NodeWF`, and
`composedDeleteRoot_keyBag` needs only `WellFormed`: each output key bag is
the input key bag after `Multiset.erase` removes one requested-key occurrence
when present (and leaves the bag unchanged when absent).  The raw and
normalized different-key membership theorems have the same structural
assumptions and do not require uniqueness or a requested-key-present premise.

Raw `composedDelete_uniqueKeys` preserves uniqueness from `NodeWF +
UniqueKeys`; it does not need root well-formedness.  At the normalized root,
`composedDeleteRoot_wellFormedUnique` preserves the combined
`WellFormedUnique` predicate.  Deleted-key absence, the complete root
membership characterization, and compatibility with the specification-level
`delete` operation require `WellFormedUnique`.  The compatibility theorems
identify membership and the membership-oracle `search`; they do not claim
`searchExec` equivalence or equality of the executable and specification tree
shapes.

## Remaining Work

Chapter 18 has no remaining core correctness group in the current functional
B-tree model: search, real top-level insertion, exact executable deletion, and
the structural minimum-key/logarithmic-height theorem are proved.

Disk-page layout, pointer mutation, page I/O counts, and RAM-cost semantics
remain optional lower-level refinements and do not reopen this correctness
milestone.
