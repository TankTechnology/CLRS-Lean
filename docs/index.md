# CLRS-Lean Documentation Index

This directory contains maintainer-facing documentation for the Lean library
and the generated Verso book.  Reader-facing chapter prose lives in
`CLRSLean/Chapter_XX.lean`; this index explains where repository-level facts
belong.

## Start Here

| Document | Purpose |
| --- | --- |
| [`../README.md`](../README.md) | Project overview, setup, and contribution contract |
| [`repository-architecture.md`](repository-architecture.md) | Code layers, dependencies, ownership, and sources of truth |
| [`proof-status-board.md`](proof-status-board.md) | Compact chapter status and next-proof priorities |
| [`proof-map.md`](proof-map.md) | Detailed theorem and proof-boundary ledger |
| [`clrs-proof-progress.csv`](clrs-proof-progress.csv) | Machine-readable chapter progress source |
| [`status/blocked-and-deferred.md`](status/blocked-and-deferred.md) | Explicitly blocked, deferred, and future work |
| [`workflows/chapter-workflow.md`](workflows/chapter-workflow.md) | End-to-end chapter formalization workflow |
| [`workflows/lean-fast-verification.md`](workflows/lean-fast-verification.md) | Narrow-to-wide Lean verification loop |
| [`site-architecture.md`](site-architecture.md) | Verso navigation, rendering, and deployment design |

## Documentation Roles

- `clrs-proof-progress.csv` owns chapter-level counts and status labels.
- `proof-map.md` owns theorem-level detail and formalization boundaries.
- `proof-status-board.md` owns prioritization; it should not duplicate every
  theorem name.
- `proof-audits/` contains dated evidence snapshots and closure records.
- `proof-patterns/` contains reusable proof-design notes.
- `chapters/` contains optional supplementary chapter notes.  The Lean chapter
  guides remain canonical.
- `research/`, `skills/`, and `superpowers/` are historical design and planning
  records, not current status sources.

## Lean Source Catalog

Chapter guides are `CLRSLean/Chapter_XX.lean`.  The represented section modules
on `main` are:

```text
CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean
CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean
CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean
CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean
CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean
CLRSLean/Chapter_04/Section_04_2_Strassen_Algorithm.lean
CLRSLean/Chapter_04/Section_04_3_Substitution_Method.lean
CLRSLean/Chapter_04/Section_04_4_Recursion_Tree_Method.lean
CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean
CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean
CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean
CLRSLean/Chapter_05/Section_05_2_Indicator_Random_Variables.lean
CLRSLean/Chapter_05/Section_05_4_Probabilistic_Analysis.lean
CLRSLean/Chapter_06/Section_06_1_Heaps.lean
CLRSLean/Chapter_06/Section_06_2_Maintaining_Heap_Property.lean
CLRSLean/Chapter_06/Section_06_3_Building_A_Heap.lean
CLRSLean/Chapter_06/Section_06_4_Heapsort.lean
CLRSLean/Chapter_06/Section_06_5_Priority_Queues.lean
CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean
CLRSLean/Chapter_07/Section_07_2_Performance_Of_Quicksort.lean
CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort.lean
CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort/Comparison_Probability.lean
CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean
CLRSLean/Chapter_08/Section_08_2_Counting_Sort/CountTables.lean
CLRSLean/Chapter_08/Section_08_2_Counting_Sort/MutableOutputArray.lean
CLRSLean/Chapter_08/Section_08_3_Radix_Sort.lean
CLRSLean/Chapter_08/Section_08_4_Bucket_Sort.lean
CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean
CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean
CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select.lean
CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean
CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean
CLRSLean/Chapter_10/Section_10_4_Rooted_Trees.lean
CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean
CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean
CLRSLean/Chapter_11/Section_11_3_Hash_Functions.lean
CLRSLean/Chapter_11/Section_11_4_Open_Addressing.lean
CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean
CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean
CLRSLean/Chapter_14/Section_14_1_Order_Statistic_Trees.lean
CLRSLean/Chapter_14/Section_14_3_Interval_Trees.lean
CLRSLean/Chapter_15/Section_15_1_Rod_Cutting.lean
CLRSLean/Chapter_15/Section_15_2_Matrix_Chain_Multiplication.lean
CLRSLean/Chapter_15/Section_15_4_Longest_Common_Subsequence.lean
CLRSLean/Chapter_15/Section_15_5_Optimal_Binary_Search_Trees.lean
CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_16/Section_16_4_Matroids.lean
CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean
CLRSLean/Chapter_17/Section_17_1_Amortized_Framework/Section_17_2_Stack_And_Counter.lean
CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables.lean
CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables/Section_17_4_Mutable_Array_Tables.lean
CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean
CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean
CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model.lean
CLRSLean/Chapter_19/Section_19_4_Bounding_Maximum_Degree.lean
CLRSLean/Chapter_20/Section_20_1_VEB_Universe.lean
CLRSLean/Chapter_20/Section_20_2_VEB_Tree.lean
CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean
CLRSLean/Chapter_21/Section_21_1_Disjoint_Set_Operations.lean
CLRSLean/Chapter_21/Section_21_2_Linked_List_Representation.lean
CLRSLean/Chapter_21/Section_21_3_Disjoint_Set_Forests.lean
CLRSLean/Chapter_21/Section_21_4_Analysis.lean
CLRSLean/Chapter_21/Section_21_4_Analysis/CostedExecution.lean
CLRSLean/Chapter_21/Section_21_4_Analysis/InverseAckermann.lean
CLRSLean/Chapter_22/Section_22_1_Representing_Graphs.lean
CLRSLean/Chapter_22/Section_22_2_BFS.lean
CLRSLean/Chapter_22/Section_22_3_DFS.lean
CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath.lean
CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals.lean
CLRSLean/Chapter_22/Section_22_3_DFS/S3_Bridge.lean
CLRSLean/Chapter_22/Section_22_3_DFS/S4_SCC.lean
CLRSLean/Chapter_22/Section_22_3_DFS/S5_EdgeClassification.lean
CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean
CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean
CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components/MergeSortCongr.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/S1_UnionFindBridge.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/S2_StatefulKruskal.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/S3_ExecutablePrim.lean
CLRSLean/Chapter_24/Section_24_1_Bellman_Ford.lean
CLRSLean/Chapter_24/Section_24_2_SSSP_In_DAGs.lean
CLRSLean/Chapter_24/Section_24_3_Dijkstra.lean
CLRSLean/Chapter_26/Section_26_1_Flow_Networks.lean
```

Reusable cross-chapter proof APIs live under `CLRSLean/ProofPatterns/`.
Stable consumer-facing checks live under `Tests/`.

## Update Rules

When a section is added or renamed, update its chapter guide,
`literate.toml`, this source catalog, and the progress CSV in the same change.
When a theorem boundary changes, update the chapter guide, progress CSV, and
proof map.  Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/check_repository.py
lake build CLRSLean
```

## Historical Records

Dated audits and old implementation plans are retained because they explain
past design decisions.  They should include a date in their filename or title
and must not be used as evidence for the current progress snapshot.
