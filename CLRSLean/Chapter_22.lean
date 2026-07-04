import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_2_BFS

/-! # Chapter 22 - Elementary Graph Algorithms

Chapter 22 introduces the finite-graph model used by the rest of the graph
algorithm track.  The current pass focuses on the mathematical layer: vertices,
adjacency, walks, paths, cycles, and reachability, plus a fuelled BFS with a
soundness proof.  Later sections add DFS, topological sort, and strongly
connected components on top of this model.

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
  and {lit}`CLRS.Chapter22.Graph.bfs_sound`.

## Current Shape

Section 22.1 establishes the public graph vocabulary.  Section 22.2 proves that
BFS only reports reachable vertices.  DFS, topological sort, and SCC are next.

## Deferred Work

* Section 22.3 DFS, parenthesis theorem, and edge classification.
* Section 22.4 Topological sort.
* Section 22.5 Strongly connected components (Kosaraju).

These are the next sprints in the phase-1 plan for CLRS chapters 1–26.
-/

namespace CLRS
namespace Chapter22

end Chapter22
end CLRS
