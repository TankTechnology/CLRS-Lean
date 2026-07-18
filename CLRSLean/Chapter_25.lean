import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model
import CLRSLean.Chapter_25.Section_25_2_Predecessor_Paths

/-!
# Chapter 25 - All-Pairs Shortest Paths

Chapter 25 generalises the single-source shortest-path machinery of Chapter 24
to the **all-pairs** setting: compute the shortest-path distance for every
ordered pair of vertices.  The chapter formalises two main families of algorithms:

1. Repeated squaring of the min-plus matrix product (Section 25.1).
2. The Floyd-Warshall algorithm with predecessor matrix and path reconstruction
   (Section 25.2).

## Sections

* 25.1 All-pairs shortest paths model and repeated-squaring DP.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.weightMatrix`,
  {lit}`CLRS.Chapter24.WeightedGraph.minPlusMul`,
  {lit}`CLRS.Chapter24.WeightedGraph.extendShortestPaths`,
  {lit}`CLRS.Chapter24.WeightedGraph.L`,
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP`.

* 25.2 Predecessor matrix and Floyd-Warshall algorithm.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.PredecessorMatrix`,
  {lit}`CLRS.Chapter24.WeightedGraph.initPredecessorMatrix`,
  {lit}`CLRS.Chapter24.WeightedGraph.floydWarshallStep`,
  {lit}`CLRS.Chapter24.WeightedGraph.floydWarshall`,
  {lit}`CLRS.Chapter24.WeightedGraph.reconstructPath`,
  {lit}`CLRS.Chapter24.WeightedGraph.hasNegCycle`,
  {lit}`CLRS.Chapter24.WeightedGraph.detectsNegCycle`.

## Current Shape

Section 25.1 defines the edge-weight matrix {lit}`W`, the min-plus matrix product
{lit}`A ◁ B`, and the inductive sequence {lit}`L^(m)` of shortest-path weights
using at most {lit}`m` edges.  It then defines {lit}`FASTER-APSP` as repeated
squaring (via {lit}`Function.iterate`).

Section 25.2 defines the predecessor matrix {lit}`Π` for path reconstruction,
the Floyd-Warshall algorithm with predecessor tracking, and negative cycle
detection via negative diagonal entries ({lit}`hasNegCycle`).  Full correctness
proofs are deferred.

## Deferred Work

* Full correctness proofs for Floyd-Warshall.
* Path reconstruction correctness ({lit}`reconstructPath_is_walk`).
* Negative-cycle detection proof (CLRS Theorem 25.3).
* Transitive closure (Section 25.2 variant).
* {lit}`O(n³ log n)` work count refinement (the current proof gives
  correctness; an explicit cost model is a separate refinement).
-/

namespace CLRS
namespace Chapter25

end Chapter25
end CLRS
