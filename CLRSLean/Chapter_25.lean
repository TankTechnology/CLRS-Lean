import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model
import CLRSLean.Chapter_25.Section_25_2_Floyd_Warshall
import CLRSLean.Chapter_25.Section_25_3_Johnsons_Algorithm

/-!
# Chapter 25 - All-Pairs Shortest Paths

Chapter 25 generalises the single-source shortest-path machinery of Chapter 24
to the **all-pairs** setting: compute the shortest-path distance for every
ordered pair of vertices.  The chapter formalises three main families of algorithms:

1. Repeated squaring of the min-plus matrix product (Section 25.1, this section).
2. The Floyd-Warshall algorithm (Section 25.2).
3. Johnson's sparse-graph algorithm (Section 25.3).

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

* 25.3 Johnson's algorithm (`Section_25_3_Johnsons_Algorithm`).
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.johnsonAugmentedGraph`,
  {lit}`CLRS.Chapter24.WeightedGraph.reweightedGraph`,
  {lit}`CLRS.Chapter24.WeightedGraph.reweightedWalkWeight_eq`,
  and {lit}`CLRS.Chapter24.WeightedGraph.reweightedWeight_nonneg`.

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
`floydWarshall` algorithm, and proves its correctness (Lemma 25.7,
Theorem 25.8, CLRS Theorem 25.3).  The predecessor matrix `Pi`,
path reconstruction `fwReconstructPath` (walk validity), and the
negative-cycle detection diagonal test are complete.  Walk-reconstruction
weight equality is deferred.

Section 25.3 defines Johnson's augmented graph and reweighted graph, proves the
telescoping identity for every walk, and proves edge-weight nonnegativity from
the potential triangle inequality.  It does not yet construct the Bellman-Ford
potential, prove shortest-path preservation, or package the repeated Dijkstra
runs into an end-to-end Johnson correctness theorem.

## Deferred Work

* Predecessor-matrix path-reconstruction weight equality
  (`walkWeight = floydWarshall`; walk validity from `Pi_adj` is proved).
* Transitive closure (Section 25.2 variant).
* Johnson's Bellman-Ford potential construction, shortest-path preservation,
  and end-to-end correctness/work theorem.
* An explicit {lit}`O(n³ log n)` work-count refinement for repeated squaring;
  Section 25.1 already proves its mathematical correctness.
-/

namespace CLRS
namespace Chapter25

end Chapter25
end CLRS
