import CLRSLean.Chapter_26.Section_26_1_Flow_Networks
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp
import CLRSLean.Chapter_26.Section_26_6_MaxFlow_MinCut

/-! # Chapter 26 - Maximum Flow

Chapter 26 opens the maximum-flow part of the CLRS graph track.  It builds a
flow-network model on top of the Chapter 22-style finite directed graph
vocabulary (using a capacity function approach) and formalizes the Ford-Fulkerson
method.

## Sections

* 26.1 Flow networks.
  Main declarations:
  {lit}`CLRS.Chapter26.FlowNetwork`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow.value`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow.netFlow_eq_value`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow.residualCapacity`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow.residualEdge`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow.augmentingPathReachable`,
  {lit}`CLRS.Chapter26.FlowNetwork.Flow.maximal_of_noAugmentingPath`.

* 26.2 Edmonds-Karp algorithm.
  Main declarations:
  {lit}`CLRS.Chapter26.ResidualPathLength`,
  {lit}`CLRS.Chapter26.IsShortestDist`,
  {lit}`CLRS.Chapter26.ShortestAugmentingPath`,
  {lit}`CLRS.Chapter26.shortest_path_nondec`.

* 26.3 Maximum bipartite matching.
  No section module is present on {lit}`main`; the flow reduction and its
  correctness remain a tracked core gap.

* 26.6 Max-Flow Min-Cut Theorem.
  Main declarations:
  {lit}`CLRS.Chapter26.Flow.eq_cutCapacity_implies_maximal`.

## Current Shape

Section 26.1 defines a {lit}`FlowNetwork` as a capacity function {lit}`c : V → V → ℝ`
together with a distinguished source {lit}`s` and sink {lit}`t`.  A feasible
flow {lit}`Flow` satisfies capacity constraint, skew symmetry, and flow
conservation.  The section proves Lemma 26.5 (net flow across any cut equals
flow value) and the generic Ford-Fulkerson correctness theorem: if there is no
augmenting path in the residual network, the flow is maximal.

Section 26.2 defines the residual path-length predicate {lit}`ResidualPathLength`
and the shortest-path distance {lit}`IsShortestDist`.  It proves the
Edmonds-Karp monotonic distance lemma (Lemma 26.7): after augmenting along a
shortest augmenting path, the distances {lit}`δ_f(s,v)` in the residual network
are nondecreasing.  This is the key lemma for the `O(VE²)` running-time bound.

The companion file `Section_26_6_MaxFlow_MinCut` proves the easy direction of the
Max-Flow Min-Cut Theorem: if `|f| = c(S,T)` for some cut, then `f` is maximal.
The converse direction (maximal `f` implies existence of such a cut) and the
full three-condition equivalence are deferred.

## Deferred Work

* The converse (and constructive) direction of the Max-Flow Min-Cut Theorem.
* The executable BFS procedure, concrete Edmonds-Karp augmenting loop, and the
  augmentation-count/{lit}`O(VE²)` theorem built from Lemma 26.7.
* Section 26.3's bipartite-matching reduction, integrality bridge, and final
  matching/flow equivalence.
-/

namespace CLRS
namespace Chapter26

end Chapter26
end CLRS
