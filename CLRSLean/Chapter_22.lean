import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_2_BFS
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_WhitePath
import CLRSLean.Chapter_22.Section_22_3_DFS_Intervals
import CLRSLean.Chapter_22.Section_22_3_DFS_SCC
import CLRSLean.Chapter_22.Section_22_3_DFS_Bridge
import CLRSLean.Chapter_22.Section_22_4_Topological_Sort
import CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components

/-! # Chapter 22 - Elementary Graph Algorithms

Chapter 22 introduces the finite-graph model used by the rest of the graph
algorithm track.  The current pass focuses on the mathematical layer: vertices,
adjacency, walks, paths, cycles, and reachability, plus a fuelled BFS with a
soundness proof.  DFS, topological sort, and the structural skeleton of
Kosaraju's strongly-connected-components algorithm are now in place.

The model intentionally mirrors the edge-list style used by CLRS pseudocode:
a finite vertex set plus an adjacency function gives a directed graph, and an
undirected graph is obtained by requiring symmetric adjacency.

## Sections

* 22.1 Representing graphs.
  Main definitions:
  {lit}`CLRS.Chapter22.Graph`,
  {lit}`CLRS.Chapter22.Graph.Adj`,
  {lit}`CLRS.Chapter22.Graph.IsWalk`,
  {lit}`CLRS.Chapter22.Graph.IsPath`,
  {lit}`CLRS.Chapter22.Graph.IsCycle`,
  {lit}`CLRS.Chapter22.Graph.Reachable`,
  {lit}`CLRS.Chapter22.Graph.ConnectedComponent`,
  {lit}`CLRS.Chapter22.Graph.reachable_refl`,
  {lit}`CLRS.Chapter22.Graph.reachable_trans`,
  and {lit}`CLRS.Chapter22.Graph.reachable_adj`.

* 22.2 Breadth-first search.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.bfsAux`,
  {lit}`CLRS.Chapter22.Graph.bfs`,
  {lit}`CLRS.Chapter22.Graph.BFSInvariant`,
  {lit}`CLRS.Chapter22.Graph.bfsInvariant_step`,
  {lit}`CLRS.Chapter22.Graph.bfsAux_sound`,
  {lit}`CLRS.Chapter22.Graph.bfs_sound`,
  and {lit}`CLRS.Chapter22.Graph.bfs_complete`.

* 22.3 Depth-first search.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.DFSState`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit`,
  {lit}`CLRS.Chapter22.Graph.dfs`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_blackens_u`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_preserves_black`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_no_new_gray`,
  {lit}`CLRS.Chapter22.Graph.dfs_all_black`,
  and {lit}`CLRS.Chapter22.Graph.dfsVisit_blackens_iff_whiteReachable`.

* 22.4 Topological sort.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.IsDAG`,
  {lit}`CLRS.Chapter22.Graph.indegree`,
  {lit}`CLRS.Chapter22.Graph.IsTopologicalOrder`,
  {lit}`CLRS.Chapter22.Graph.topologicalSort`,
  and {lit}`CLRS.Chapter22.Graph.topologicalSort_isTopologicalOrder`.

* 22.5 Strongly connected components.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.transpose`,
  {lit}`CLRS.Chapter22.Graph.StronglyConnected`,
  {lit}`CLRS.Chapter22.Graph.IsSCC`,
  {lit}`CLRS.Chapter22.Graph.IsSCCPartition`,
  {lit}`CLRS.Chapter22.Graph.dfsFromListCollect`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_subset`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_pairwise_disjoint`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_cover`,
  and {lit}`CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition`.

## Current Shape

Section 22.1 establishes the public graph vocabulary.  Section 22.2 proves that
BFS is both sound (only reachable vertices are reported) and complete (every
reachable vertex is reported).  Section 22.3 gives a functional DFS model and
proves that every vertex of the graph is black after {lit}`dfs`.  Section 22.4
implements Kahn's algorithm and proves that it returns a valid topological order
for every DAG.  Section 22.5 implements Kosaraju's two-pass SCC algorithm and
proves the structural partition properties (subsets of vertices, pairwise
disjointness, coverage, and nonemptiness); the SCC strong-connectivity and
maximality theorem is reduced to a standard DFS finish-time ordering lemma and
is currently admitted with {lit}`sorry`.

## Deferred Work

* Section 22.3: parenthesis theorem and edge classification.  The white-path
  theorem ({lit}`CLRS.Chapter22.Graph.dfsVisit_blackens_iff_whiteReachable`) is
  now proved in {lit}`CLRSLean.Chapter_22.Section_22_3_DFS_Theory`.
* Section 22.5: the DFS finish-time lemma that implies each collected Kosaraju
  component is strongly connected and maximal.

These are the next sprints in the phase-1 plan for CLRS chapters 1–26.
-/

namespace CLRS
namespace Chapter22

end Chapter22
end CLRS
