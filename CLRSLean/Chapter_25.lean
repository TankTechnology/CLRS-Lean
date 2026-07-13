import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model
import CLRSLean.Chapter_25.Section_25_2_Floyd_Warshall
import CLRSLean.Chapter_25.Section_25_3_Johnsons_Algorithm

/-!
# Chapter 25 - All-Pairs Shortest Paths

Chapter 25 generalises the single-source shortest-path machinery of Chapter 24
to the **all-pairs** setting: compute the shortest-path distance for every
ordered pair of vertices.  The chapter formalises two main families of algorithms:

1. Repeated squaring of the min-plus matrix product (Section 25.1, this section).
2. The Floyd-Warshall algorithm (Section 25.2).

## Sections

* 25.1 All-pairs shortest paths model and repeated-squaring DP.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.weightMatrix`,
  {lit}`CLRS.Chapter24.WeightedGraph.minPlusMul`,
  {lit}`CLRS.Chapter24.WeightedGraph.extendShortestPaths`,
  {lit}`CLRS.Chapter24.WeightedGraph.L`,
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP`,
  {lit}`CLRS.Chapter24.WeightedGraph.lemma_25_1`,
  {lit}`CLRS.Chapter24.WeightedGraph.L_sq_eq_minPlusMul` (Lemma 25.2),
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_L`,
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_shortestDist`.

* 25.2 Floyd-Warshall (`Section_25_2_Floyd_Warshall`).
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.fwStep`,
  {lit}`CLRS.Chapter24.WeightedGraph.D`,
  {lit}`CLRS.Chapter24.WeightedGraph.floydWarshall`,
  {lit}`CLRS.Chapter24.WeightedGraph.floydWarshall_O_cubed`.

## Current Shape

Section 25.1 defines the edge-weight matrix {lit}`W`, the min-plus matrix product
{lit}`A ◁ B`, and the inductive sequence {lit}`L^(m)` of shortest-path weights
using at most {lit}`m` edges.  It then defines {lit}`FASTER-APSP` as repeated
squaring (via {lit}`Function.iterate`) and proves:

* Lemma 25.1: {lit}`L^(m+1)_ij = min_k (L^m_ik + w_kj)`.
* Lemma 25.2 (squaring identity): {lit}`L^(2m) = L^m ◁ L^m`.
* Under no negative-weight cycles, {lit}`L^m = L^{|V|-1}` for all {lit}`m ≥ |V|-1`.
* {lit}`fasterAPSP = L^{|V|-1} = δ`, the all-pairs shortest-path matrix
  ({lit}`fasterAPSP_eq_shortestDist`).

Section 25.2 defines the Floyd-Warshall DP recurrence `D` and the
`floydWarshall` algorithm.  The Θ(V³) work bound is recorded.  The
correctness proofs (Lemma 25.7 and Theorem 25.8) are deferred.

## Deferred Work

* Floyd-Warshall correctness: `D_le_simple` and `D_attainable` lemmas.
* Predecessor matrix {lit}`Π` and path reconstruction.
* Negative-cycle detection (CLRS Theorem 25.3).
* Transitive closure (Section 25.2 variant).
* {lit}`O(n³ log n)` work count refinement (the current proof gives
  correctness; an explicit cost model is a separate refinement).
-/

namespace CLRS
namespace Chapter25

end Chapter25
end CLRS
