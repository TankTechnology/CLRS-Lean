# Chapter 22 Closure Audit

Date: 2026-07-10

Status: `main-proof-complete-for-correctness`

Core completion commit: `1aeb257`

## Acceptance Boundary

The Chapter 22 seal covers the main functional-correctness claims in Sections
22.1-22.5 on the repository's finite directed-graph model.  It does not claim a
line-by-line imperative refinement, a RAM semantics, exact `O(V + E)` work
accounting, exercises, or chapter-end problems.

## Source Directory

| Section | Source | Responsibility |
| --- | --- | --- |
| 22.1 | `CLRSLean/Chapter_22/Section_22_1_Representing_Graphs.lean` | Finite graph model, walks, paths, cycles, reachability, undirected symmetry |
| 22.2 | `CLRSLean/Chapter_22/Section_22_2_BFS.lean` | Reachability BFS, shortest distances, labelled FIFO state, predecessor tree |
| 22.3 | `CLRSLean/Chapter_22/Section_22_3_DFS.lean` | DFS state, colors, timestamps, parents, global traversal facts |
| 22.3 | `CLRSLean/Chapter_22/Section_22_3_DFS/WhitePath.lean` | White-path theorem |
| 22.3 | `CLRSLean/Chapter_22/Section_22_3_DFS/Intervals.lean` | Parenthesis theorem and ancestor/interval characterization |
| 22.3 | `CLRSLean/Chapter_22/Section_22_3_DFS/Bridge.lean` | Discovery-state and SCC bridge lemmas |
| 22.3 | `CLRSLean/Chapter_22/Section_22_3_DFS/SCC.lean` | DFS finish-time facts used by SCCs |
| 22.3 | `CLRSLean/Chapter_22/Section_22_3_DFS/EdgeClassification.lean` | Unique tree/back/forward/cross classification and timestamp characterizations |
| 22.4 | `CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean` | Kahn and DFS finish-time topological sorts |
| 22.5 | `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean` | Kosaraju implementation and SCC-partition correctness |
| 22.5 | `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components/MergeSortCongr.lean` | Comparator congruence for decreasing finish-time sorting |

## Closure Theorems

- `Graph.bfsState_correct`: exact unweighted shortest distances and rooted
  predecessor-tree correctness for the labelled FIFO BFS.
- `Graph.dfs_parenthesis`: final DFS intervals are disjoint or nested.
- `Graph.dfs_edge_classification_unique`: every directed edge has exactly one
  CLRS DFS edge kind.
- `Graph.dfsTopologicalSort_isTopologicalOrder`: decreasing DFS finish time is
  a topological order for DAGs.
- `Graph.kosarajuComponents_isSCCPartition`: Kosaraju returns a nonempty,
  pairwise-disjoint, covering partition into maximal strongly connected sets.

## Verification Evidence

- `lake env lean CLRSLean/Chapter_22/Section_22_2_BFS.lean`
- `lake build CLRSLean.Chapter_22`
- `lake env lean Tests/Chapter_22_Interface.lean`
- `lake env lean Tests/Chapter_22_Closure.lean`
- `lake build`
- `python3 scripts/check_progress_csv.py`
- `python3 scripts/check_site_consistency.py`
- `python3 scripts/test_literate_config.py LiterateConfigTest.test_chapter_imported_sections_are_ordered_and_titled`
- unfinished-proof marker scan over `CLRSLean/Chapter_22`

`Tests/Chapter_22_Closure.lean` also prints the axiom dependencies of the five
closure theorems.  They use only the standard classical/propositional axioms
expected by the current noncomputable finite-set model; no project-specific
axiom is introduced.

## Deferred Refinements

- Explicit work measures and `O(V + E)` bounds.
- Imperative adjacency-list and RAM-semantics refinements.
- Exercises and chapter-end problems.

These refinements may extend Chapter 22 without changing its sealed core
correctness status.
