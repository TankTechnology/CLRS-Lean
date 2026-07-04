import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Chapter 22 - Elementary Graph Algorithms

Chapter 22 introduces the finite-graph model used by the rest of the graph
algorithm track.  The current pass focuses on the mathematical layer: vertices,
adjacency, walks, paths, cycles, and reachability.  Later sections add BFS, DFS,
topological sort, and strongly connected components on top of this model.

The model intentionally mirrors the edge-list style used by CLRS pseudocode:
a finite vertex set plus an adjacency function gives a directed graph, and an
undirected graph is obtained by requiring symmetric adjacency.

## Sections

* 22.1 Representing graphs: {lit}`partial`.
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

## Current Shape

Section 22.1 establishes the public graph vocabulary.  BFS/DFS/topological sort
and SCC will build executable algorithms and correctness proofs on this layer.

## Deferred Work

* Section 22.2 BFS and shortest paths in unweighted graphs.
* Section 22.3 DFS, parenthesis theorem, and edge classification.
* Section 22.4 Topological sort.
* Section 22.5 Strongly connected components (Kosaraju).

These are the next sprints in the phase-1 plan for CLRS chapters 1–26.
-/

namespace CLRS
namespace Chapter22

end Chapter22
end CLRS
