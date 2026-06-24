# CLRS-Lean

`CLRS-Lean` is a chapter-by-chapter Lean companion project for CLRS-style
algorithm correctness proofs.

The project is organized by the book order, not by implementation topic.  A
section file is named with both its CLRS number and a short human-readable
suffix:

```text
CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean
CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean
CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean
CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean
CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean
CLRSLean/Chapter_04/Section_04_3_Substitution_Method.lean
CLRSLean/Chapter_04/Section_04_4_Recursion_Tree_Method.lean
CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean
CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean
CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean
CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean
CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean
CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean
CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean
CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean
CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
```

In prose and on the future website, these appear as:

- Section 2.1 - Insertion sort
- Section 2.2 - Analyzing algorithms
- Section 2.3 - Designing algorithms
- Section 3.1 - Asymptotic notation
- Section 3.2 - Standard functions
- Section 4.1 - The maximum-subarray problem
- Section 4.3 - The substitution method
- Section 4.4 - The recursion-tree method
- Section 4.5 - The master method
- Section 5.1 - The hiring problem
- Section 10.1 - Stacks and queues
- Section 10.2 - Linked lists
- Section 11.1 - Direct-address tables
- Section 11.2 - Chained hash tables
- Section 12.1 - Binary search trees
- Section 13.1 - Red-black trees
- Section 16.1 - Activity selection
- Section 16.3 - Huffman codes
- Section 23.1 - Growing a minimum spanning tree
- Section 23.2 - Kruskal and Prim

The Lean filenames use underscores instead of hyphens because Lean module names
should remain import-friendly.

## Current Sections

| CLRS section | Lean source | Status | Main result |
| --- | --- | --- | --- |
| Section 2.1 - Insertion sort | `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean` | `proved` | `CLRS.Chapter02.insertionSort_sorted`, `CLRS.Chapter02.insertionSort_perm` |
| Section 2.2 - Analyzing algorithms | `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean` | `proved` | `CLRS.Chapter02.insertionSortWorstComparisons_quadratic` |
| Section 2.3 - Designing algorithms | `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean` | `proved` | `CLRS.Chapter02.mergeSort_sortedLE`, `CLRS.Chapter02.mergeSort_perm`, `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm` |
| Section 3.1 - Asymptotic notation | `CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean` | `proved` | `CLRS.Chapter03.isBigO_iff`, `CLRS.Chapter03.isLittleO_iff`, `CLRS.Chapter03.isBigTheta_trans` |
| Section 3.2 - Standard functions | `CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean` | `partial` | `CLRS.Chapter03.isLittleO_pow_pow`, `CLRS.Chapter03.isLittleO_pow_const_exp`, `CLRS.Chapter03.isLittleO_log_rpow`, `CLRS.Chapter03.isLittleO_exp_vs_factorial` |
| Section 4.1 - Maximum subarray | `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean` | `proved` for the exhaustive-search specification | `CLRS.Chapter04.mem_nonemptySubarrays_iff`, `CLRS.Chapter04.bestCandidate_correct`, `CLRS.Chapter04.maxSubarray_exists_of_ne_nil`, `CLRS.Chapter04.maxSubarray_correct` |
| Section 4.2 - Strassen's algorithm | not yet created | `future-work` | planned block-matrix correctness proof |
| Section 4.3 - Substitution method | `CLRSLean/Chapter_04/Section_04_3_Substitution_Method.lean` | `proved` for one-step recurrence bounds | `CLRS.Chapter04.substitution_upper_bound`, `CLRS.Chapter04.linear_substitution_upper_bound`, `CLRS.Chapter04.geometric_substitution_upper_bound` |
| Section 4.4 - Recursion-tree method | `CLRSLean/Chapter_04/Section_04_4_Recursion_Tree_Method.lean` | `proved` for additive level-cost expansions | `CLRS.Chapter04.recursion_tree_additive_unroll`, `CLRS.Chapter04.recursion_tree_additive_upper_envelope`, `CLRS.Chapter04.recursion_tree_constant_level_cost` |
| Section 4.5 - The master method | `CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean` | `proved` for exact powers | `CLRS.Chapter04.master_case1_geometric`, `CLRS.Chapter04.master_case2_constant_forcing`, `CLRS.Chapter04.master_case3_tail_dominated` |
| Section 4.6 - Proof of the master theorem | not yet created | `future-work` | planned extension from exact powers to all input sizes |
| Section 5.1 - The hiring problem | `CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean` | `proved` for finite rank symmetry | `CLRS.Chapter05.hireProbability_eq`, `CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic` |
| Section 10.1 - Stacks and queues | `CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean` | `proved` | `CLRS.Chapter10.pop_push`, `CLRS.Chapter10.dequeue_enqueue_nonempty` |
| Section 10.2 - Linked lists | `CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean` | `proved` | `CLRS.Chapter10.listSearch_sound`, `CLRS.Chapter10.mem_listDeleteAll_iff` |
| Section 11.1 - Direct-address tables | `CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean` | `proved` | `CLRS.Chapter11.search_insert_same`, `CLRS.Chapter11.search_delete_same` |
| Section 11.2 - Chained hash tables | `CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean` | `partial` | `CLRS.Chapter11.hashSearch_hashInsert_self`, `CLRS.Chapter11.hashSearch_hashInsert_iff`, `CLRS.Chapter11.hashSearch_hashDelete_self`, `CLRS.Chapter11.hashSearch_hashDelete_iff` |
| Section 12.1 - Binary search trees | `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean` | `partial` | `CLRS.Chapter12.BSTree.search_eq_true_iff`, `CLRS.Chapter12.BSTree.minimum?_le_of_ordered`, `CLRS.Chapter12.BSTree.le_maximum?_of_ordered`, `CLRS.Chapter12.BSTree.successor?_least_greater`, `CLRS.Chapter12.BSTree.predecessor?_greatest_less`, `CLRS.Chapter12.BSTree.insert_ordered`, `CLRS.Chapter12.BSTree.inTree_delete_iff`, `CLRS.Chapter12.BSTree.delete_ordered` |
| Section 13.1 - Red-black trees | `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean` | `partial` | `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`, `CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`, `CLRS.Chapter13.RBTree.noRedRed_repaint_black`, `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`, `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`, `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`, `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`, `CLRS.Chapter13.RBTree.redBlackShape_repaint_black` |
| Section 16.1 - Activity selection | `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean` | `partial` | `CLRS.ActivitySelection.finishSorted_head_minFinish`, `CLRS.ActivitySelection.greedySelect_sublist`, `CLRS.ActivitySelection.greedySelect_feasible`, `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate` |
| Section 16.3 - Huffman codes | `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean` | `proved` | `HuffmanV2.optimum_huffman_freqs` |
| Section 23.1 - Growing a minimum spanning tree | `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean` | `partial` | `CLRS.MST.safe_edge_of_lightest_crossing` |
| Section 23.2 - Kruskal and Prim | `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean` | `partial` | `CLRS.MST.kruskal_optimal` |

See [`proof-map.md`](proof-map.md) for the full status ledger.

The public website is generated from the Lean files by Verso.  The landing page
is `CLRSLean.lean`; chapter guide pages live at `CLRSLean/Chapter_XX.lean`; the
status ledger and workflow page live at `CLRSLean/Status.lean` and
`CLRSLean/Workflow.lean`.

## Status Labels

- `proved`: the main theorem for this section is sorry-free.
- `partial`: important Lean theorems exist, but the full CLRS section is not
  complete.
- `statement`: theorem interfaces exist, but proofs have not started.
- `blocked-design`: progress depends on choosing a representation, such as
  graph paths, heaps, arrays, or probability spaces.
- `blocked-mathlib`: progress depends on missing or inconvenient Mathlib
  infrastructure.
- `deferred-implementation`: the mathematical proof is in scope, but a low-level
  implementation proof is intentionally postponed.
- `future-work`: useful extension work, such as exercises or chapter-end
  Problems, that is intentionally outside the first main-theorem pass.
- `out-of-scope`: the section is not a current project target.

## Near-Term Rule

For early CLRS work, implementation-level data structure proofs are optional.
For example, union-find correctness is recorded as
`deferred-implementation`; the main MST target is the mathematical CLRS proof
via cut certificates and Kruskal's safe-edge induction.
