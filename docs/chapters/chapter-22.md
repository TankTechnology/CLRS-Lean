# Chapter 22 - Elementary Graph Algorithms

- Chapter status: `main-proof-complete-for-correctness`
- Sealed: `2026-07-10`
- Core completion commit: `1aeb257`
- Closure audit: `docs/proof-audits/chapter-22-closure-2026-07-10.md`

The seal covers the advertised functional-correctness surface of Sections
22.1-22.5.  Exercises, chapter-end problems, and explicit work/RAM-cost models
remain follow-up tracks and do not reopen the core correctness milestone.

## Section 22.1 - Representing Graphs

- Lean source: `CLRSLean/Chapter_22/Section_22_1_Representing_Graphs.lean`
- Status: `proved`
- Main declarations:
  `CLRS.Chapter22.Graph`,
  `CLRS.Chapter22.Graph.Adj`,
  `CLRS.Chapter22.Graph.IsWalk`,
  `CLRS.Chapter22.Graph.IsPath`,
  `CLRS.Chapter22.Graph.IsCycle`,
  `CLRS.Chapter22.Graph.Reachable`,
  `CLRS.Chapter22.Graph.ConnectedComponent`,
  `CLRS.Chapter22.Graph.reachable_refl`,
  `CLRS.Chapter22.Graph.reachable_trans`, and
  `CLRS.Chapter22.Graph.reachable_adj`

This section establishes the finite directed-graph model used by the rest of the
Chapter 22 track: a finite vertex set with a decidable adjacency function, plus
walk/path/cycle predicates, reachability, connected components, and undirected
graph symmetry.

## Section 22.2 - Breadth-First Search

- Lean source: `CLRSLean/Chapter_22/Section_22_2_BFS.lean`
- Status: `proved`
- Main declarations:
  `CLRS.Chapter22.Graph.bfsAux`,
  `CLRS.Chapter22.Graph.bfs`,
  `CLRS.Chapter22.Graph.BFSInvariant`,
  `CLRS.Chapter22.Graph.bfsInvariant_step`,
  `CLRS.Chapter22.Graph.bfsAux_sound`,
  `CLRS.Chapter22.Graph.bfs_sound`,
  `CLRS.Chapter22.Graph.bfs_complete`,
  `CLRS.Chapter22.Graph.bfsState`,
  `CLRS.Chapter22.Graph.bfsState_distance_eq_some_iff`,
  `CLRS.Chapter22.Graph.bfsState_isBFSPredecessorTree`, and
  `CLRS.Chapter22.Graph.bfsState_correct`

A fuelled functional BFS is defined on the Section 22.1 graph model, and
`bfs_sound` proves that every vertex reported as visited by BFS is reachable from
the source.  Conversely, `bfs_complete` proves that every reachable vertex is
reported.  The CLRS-labelled FIFO state additionally records distance and
parent functions.  `bfsState_distance_eq_some_iff` characterizes every label as
the exact unweighted shortest-path distance.  The predecessor-tree theorem
proves that parents are defined exactly on reachable non-source vertices, are
graph edges with a unit distance increment, recover a root path of the recorded
length, and form an acyclic relation.

## Section 22.3 - Depth-First Search

- Lean sources:
  `CLRSLean/Chapter_22/Section_22_3_DFS.lean`,
  `CLRSLean/Chapter_22/Section_22_3_DFS/WhitePath.lean`,
  `CLRSLean/Chapter_22/Section_22_3_DFS/Intervals.lean`,
  `CLRSLean/Chapter_22/Section_22_3_DFS/Bridge.lean`,
  `CLRSLean/Chapter_22/Section_22_3_DFS/SCC.lean`, and
  `CLRSLean/Chapter_22/Section_22_3_DFS/EdgeClassification.lean`
- Status: `proved`
- Main declarations:
  `CLRS.Chapter22.Graph.DFSState`,
  `CLRS.Chapter22.Graph.dfsVisit`,
  `CLRS.Chapter22.Graph.dfs`,
  `CLRS.Chapter22.Graph.dfsVisit_blackens_u`,
  `CLRS.Chapter22.Graph.dfsVisit_preserves_black`,
  `CLRS.Chapter22.Graph.dfsVisit_no_new_gray`,
  `CLRS.Chapter22.Graph.dfs_all_black`,
  `CLRS.Chapter22.Graph.dfsVisit_blackens_iff_whiteReachable`,
  `CLRS.Chapter22.Graph.dfs_parenthesis`,
  `CLRS.Chapter22.Graph.dfs_intervals_not_cross`,
  `CLRS.Chapter22.Graph.IsDFSAncestor_reachable`,
  `CLRS.Chapter22.Graph.dfs_parent_discovery_lt`,
  `CLRS.Chapter22.Graph.intervalNestedInside_dfs_implies_ancestor`,
  `CLRS.Chapter22.Graph.intervalNestedInside_dfs_iff_ancestor`,
  `CLRS.Chapter22.Graph.DFSEdgeKind`,
  `CLRS.Chapter22.Graph.dfs_edge_classification_unique`,
  `CLRS.Chapter22.Graph.dfs_tree_or_forward_edge_iff_timestamps`,
  `CLRS.Chapter22.Graph.dfs_back_edge_iff_timestamps`,
  `CLRS.Chapter22.Graph.dfs_cross_edge_iff_timestamps`,
  `CLRS.Chapter22.Graph.dfs_undirected_edge_tree_or_back`, and
  `CLRS.Chapter22.Graph.exists_discovery_state`

A functional depth-first-search model with white/gray/black colors, discovery
and finish timestamps, and parent pointers is defined.  The basic color
invariants are proved, and `dfs_all_black` states that every vertex of the graph
is black after a complete `dfs`.  The white-path development proves that a
sufficiently fuelled visit blackens exactly the white-reachable set.  Timestamp,
discovery-state, ancestor, parent-edge, and SCC finish-time infrastructure is
also proved.  `dfs_parenthesis` proves that the final discovery/finish intervals
of distinct graph vertices are disjoint or strictly nested, and
`dfs_intervals_not_cross` rules out partial overlap.  The theorem
`intervalNestedInside_dfs_iff_ancestor` completes the parent-forest
characterization: for distinct graph vertices, strict interval containment is
equivalent to ancestry.  Finally, every graph edge is proved to have exactly one
tree/back/forward/cross kind, with the standard CLRS timestamp characterizations;
self-loops are back edges, and every undirected edge is tree or back.

## Section 22.4 - Topological Sort

- Lean source: `CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean`
- Status: `proved` for both Kahn and CLRS DFS finish-time models
- Main declarations:
  `CLRS.Chapter22.Graph.IsDAG`,
  `CLRS.Chapter22.Graph.indegree`,
  `CLRS.Chapter22.Graph.IsTopologicalOrder`,
  `CLRS.Chapter22.Graph.topologicalSort`,
  `CLRS.Chapter22.Graph.topologicalSort_isTopologicalOrder`,
  `CLRS.Chapter22.Graph.dfs_finish_time_decreases_on_dag_edge`,
  `CLRS.Chapter22.Graph.dfsTopologicalSort`, and
  `CLRS.Chapter22.Graph.dfsTopologicalSort_isTopologicalOrder`

Kahn's algorithm is defined on the Section 22.1 graph model.  The main theorem
`topologicalSort_isTopologicalOrder` proves that `topologicalSort` returns a
valid topological order whenever the input graph is a DAG.  The implementation
uses a fuelled recursive loop and the axiom of choice to pick a current source
vertex.

The CLRS version runs DFS and sorts vertices by decreasing finish time.
`dfs_finish_time_decreases_on_dag_edge` proves that every DAG edge `u → v`
satisfies `f[v] < f[u]`; `dfsTopologicalSort_isTopologicalOrder` then turns the
sorted finish-time relation into the required list-index ordering.

## Section 22.5 - Strongly Connected Components

- Lean sources:
  `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean` and
  `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components/MergeSortCongr.lean`
- Status: `proved`
- Main declarations:
  `CLRS.Chapter22.Graph.transpose`,
  `CLRS.Chapter22.Graph.StronglyConnected`,
  `CLRS.Chapter22.Graph.IsSCC`,
  `CLRS.Chapter22.Graph.kosarajuComponents`,
  `CLRS.Chapter22.Graph.scc_finish_time_order`,
  `CLRS.Chapter22.Graph.scc_finish_order`,
  `CLRS.Chapter22.Graph.kosarajuComponents_eq_sccs`, and
  `CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition`

Kosaraju's two-pass algorithm is implemented and fully connected to the SCC
specification.  The first-pass finish-time ordering is proved, the second-pass
DFS tree is proved to be exactly one SCC, and the final output is proved to be a
nonempty, pairwise-disjoint, covering partition into strongly connected maximal
components.

## Remaining Chapter Work

- explicit algorithm-cost models for the functional implementations.
