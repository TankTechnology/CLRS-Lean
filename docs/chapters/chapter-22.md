# Chapter 22 - Elementary Graph Algorithms

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
- Status: `partial`
- Main declarations:
  `CLRS.Chapter22.Graph.bfsAux`,
  `CLRS.Chapter22.Graph.bfs`,
  `CLRS.Chapter22.Graph.BFSInvariant`,
  `CLRS.Chapter22.Graph.bfsInvariant_step`,
  `CLRS.Chapter22.Graph.bfsAux_sound`, and
  `CLRS.Chapter22.Graph.bfs_sound`

A fuelled functional BFS is defined on the Section 22.1 graph model, and
`bfs_sound` proves that every vertex reported as visited by BFS is reachable from
the source.  Reachability completeness and unweighted shortest-path distances
remain open.

## Section 22.3 - Depth-First Search

- Lean source: `CLRSLean/Chapter_22/Section_22_3_DFS.lean`
- Status: `partial`
- Main declarations:
  `CLRS.Chapter22.Graph.DFSState`,
  `CLRS.Chapter22.Graph.dfsVisit`,
  `CLRS.Chapter22.Graph.dfs`,
  `CLRS.Chapter22.Graph.dfsVisit_blackens_u`,
  `CLRS.Chapter22.Graph.dfsVisit_preserves_black`,
  `CLRS.Chapter22.Graph.dfsVisit_no_new_gray`, and
  `CLRS.Chapter22.Graph.dfs_all_black`

A functional depth-first-search model with white/gray/black colors, discovery
and finish timestamps, and parent pointers is defined.  The basic color
invariants are proved, and `dfs_all_black` states that every vertex of the graph
is black after a complete `dfs`.  The parenthesis theorem, white-path theorem,
and edge classification are still to come.

## Section 22.4 - Topological Sort

- Lean source: `CLRSLean/Chapter_22/Section_22_4_Topological_Sort.lean`
- Status: `partial`
- Main declarations:
  `CLRS.Chapter22.Graph.IsDAG`,
  `CLRS.Chapter22.Graph.indegree`,
  `CLRS.Chapter22.Graph.IsTopologicalOrder`,
  `CLRS.Chapter22.Graph.topologicalSort`, and
  `CLRS.Chapter22.Graph.topologicalSort_isTopologicalOrder`

Kahn's algorithm is defined on the Section 22.1 graph model.  The main theorem
`topologicalSort_isTopologicalOrder` proves that `topologicalSort` returns a
valid topological order whenever the input graph is a DAG.  The implementation
uses a fuelled recursive loop and the axiom of choice to pick a current source
vertex.

Open tasks:

- DFS-based topological sort (to match the CLRS presentation more closely);
- parenthesis theorem and white-path theorem;
- DFS edge classification (tree/back/forward/cross edges);
- Section 22.5 strongly connected components (Kosaraju).
