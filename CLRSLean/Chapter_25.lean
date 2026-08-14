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
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSP_eq_shortestDist`,
  {lit}`CLRS.Chapter24.WeightedGraph.minPlusMulCost`,
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSPCost`,
  {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_cubed_log` (O(V³ log V)),
  and {lit}`CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_four`.

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
  {lit}`CLRS.Chapter24.WeightedGraph.reweightedWeight_nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.johnsonCost_eq` (O(V² log V + V E log V)),
  and {lit}`CLRS.Chapter24.WeightedGraph.johnsonCost_le`.

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
path reconstruction `fwReconstructPath` (walk validity and **weight
equality**), and the negative-cycle detection diagonal test are all
complete.

Section 25.3 defines Johnson's augmented graph and reweighted graph,
constructs the Bellman-Ford potential `h(v) = δ(none, some v)`, proves
the triangle inequality `h(v) ≤ h(u) + w(u, v)`, proves reweighted
edge-weight nonnegativity, packages the end-to-end Johnson
correctness theorem `johnsonDist_isShortestDist` (CLRS Theorem 25.5),
and records the `O(V² log V + V E log V)` binary-heap work bound
(`johnsonCost_eq` / `johnsonCost_le`).

## Running-time layer

All three algorithms now carry explicit, reader-facing running-time theorems
bound to their real executable constructions:

* Section 25.1: `minPlusMulCost` / `fasterAPSPCost` bound to the actual graph
  `G` and iteration count `numSquarings`; `fasterAPSPCost_le_n_cubed_log`
  proves the `O(V³ log V)` repeated-squaring bound, with the trivial `O(V⁴)`
  corollary `fasterAPSPCost_le_n_four`.
* Section 25.2: `fwStepCost` / `floydWarshallCost` count the actual
  `D` recurrence over `Finset.univ.toList`, and `floydWarshall_O_cubed`
  proves the exact `O(V³)` bound.
* Section 25.3: `johnsonAugmentedGraph_edges_card` proves the augmented graph
  has `|V| + |E|` edges; `johnsonCost_eq` / `johnsonCost_le` prove the
  `O(V² log V + V E log V)` binary-heap bound.

## Deferred Work

* Lower-level RAM / mutable-array machine-arithmetic accounting for the cost
  models; the reader-facing asymptotic bounds above are proved, and concrete
  word-level constants remain an optional refinement.
-/

namespace CLRS
namespace Chapter25

end Chapter25
end CLRS
