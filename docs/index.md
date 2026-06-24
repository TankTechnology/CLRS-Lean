# CLRS-lean

`CLRS-lean` is a chapter-by-chapter Lean companion project for CLRS-style
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
| Section 3.2 - Standard functions | `CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean` | `partial` | `CLRS.Chapter03.isLittleO_pow_pow`, `CLRS.Chapter03.isLittleO_exp_vs_factorial` |
| Section 10.1 - Stacks and queues | `CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean` | `proved` | `CLRS.Chapter10.pop_push`, `CLRS.Chapter10.dequeue_enqueue_nonempty` |
| Section 10.2 - Linked lists | `CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean` | `proved` | `CLRS.Chapter10.listSearch_sound`, `CLRS.Chapter10.mem_listDeleteAll_iff` |
| Section 11.1 - Direct-address tables | `CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean` | `proved` | `CLRS.Chapter11.search_insert_same`, `CLRS.Chapter11.search_delete_same` |
| Section 11.2 - Chained hash tables | `CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean` | `partial` | `CLRS.Chapter11.hashSearch_hashInsert_self` |
| Section 12.1 - Binary search trees | `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean` | `partial` | `CLRS.Chapter12.BSTree.inTree_insert_iff`, `CLRS.Chapter12.BSTree.insert_ordered` |
| Section 13.1 - Red-black trees | `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean` | `partial` | `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`, `CLRS.Chapter13.RBTree.noRedRed_repaint_black` |
| Section 16.1 - Activity selection | `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean` | `partial` | `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate` |
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
