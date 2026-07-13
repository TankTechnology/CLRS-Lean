import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model
import CLRSLean.Chapter_25.Section_25_2_Floyd_Warshall

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
  {lit}`CLRS.Chapter25.AllPairs.weightMatrix`,
  {lit}`CLRS.Chapter25.AllPairs.minPlusMul`,
  {lit}`CLRS.Chapter25.AllPairs.extendShortestPaths`,
  {lit}`CLRS.Chapter25.AllPairs.L`,
  {lit}`CLRS.Chapter25.AllPairs.fasterAPSP`,
  {lit}`CLRS.Chapter25.AllPairs.lemma_25_1`,
  {lit}`CLRS.Chapter25.AllPairs.L_sq_eq_minPlusMul` (Lemma 25.2),
  {lit}`CLRS.Chapter25.AllPairs.fasterAPSP_eq_L`,
  {lit}`CLRS.Chapter25.AllPairs.fasterAPSP_eq_shortestDist`.

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

The proof uses the link to Chapter 24's {lit}`relaxDist` and {lit}`NoNegCycle`,
avoiding a separate triangle-inequality fixpoint argument by leveraging
monotonicity of {lit}`L` and the walk-attainability lemma.

## Deferred Work

* Floyd-Warshall (Section 25.2).
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
