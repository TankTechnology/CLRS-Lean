import CLRSLean.Chapter_24.Section_24_0_Weighted_Graphs

/-! # Chapter 24 - Single-Source Shortest Paths

Chapter 24 covers algorithms for finding shortest paths from a single source
vertex to all other vertices in an edge-weighted directed graph.

## Sections

* 24.0 Weighted graphs and shortest-path weights.
  Main definitions:
  {lit}`CLRS.Chapter24.WeightedGraph`,
  {lit}`CLRS.Chapter24.WeightedGraph.walkWeight`,
  {lit}`CLRS.Chapter24.WeightedGraph.δ`.

## Current Shape

Section 24.0 contains the weighted-graph model extended from Section 22.1:
edge-weighted graphs, walk weight sums, and the shortest-path weight δ(s,v)
defined as the infimum of all walk weights.

## Deferred Work

* Section 24.1 (The Bellman-Ford algorithm).
* Section 24.2 (Single-source shortest paths in directed acyclic graphs).
* Section 24.3 (Dijkstra's algorithm).
* Section 24.4 (Difference constraints and shortest paths).
* Section 24.5 (Proofs of shortest-paths properties).
-/

namespace CLRS
namespace Chapter24

end Chapter24
end CLRS
