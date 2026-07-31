import CLRSLean.Chapter_26.Section_26_1_Flow_Networks
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.Ford_Fulkerson_Augmentation
import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.Chapter_26.Section_26_6_MaxFlow_MinCut

/-! # Chapter 26 - Maximum Flow

Chapter 26 opens the maximum-flow part of the CLRS graph track.  The current
partial development builds a finite capacity-function model, proves the core
flow/cut foundation, and exposes infrastructure for the later algorithms.

## Sections

* 26.1 Flow networks.
  Main declarations:
  {lit}`CLRS.Chapter26.FlowNetwork`,
  {lit}`CLRS.Chapter26.Flow`,
  {lit}`CLRS.Chapter26.Flow.value`,
  {lit}`CLRS.Chapter26.Flow.netFlow_eq_value`,
  {lit}`CLRS.Chapter26.Flow.residualCapacity`,
  {lit}`CLRS.Chapter26.Flow.residualEdge`,
  {lit}`CLRS.Chapter26.Flow.augmentingPathReachable`,
  {lit}`CLRS.Chapter26.Flow.maximal_of_noAugmentingPath`.

* 26.2 Ford-Fulkerson augmentation (partial).
  Main declarations:
  {lit}`CLRS.Chapter26.Flow.ResidualPath`,
  {lit}`CLRS.Chapter26.Flow.AugmentingPath`,
  {lit}`CLRS.Chapter26.Flow.AugmentingPath.bottleneck`,
  {lit}`CLRS.Chapter26.Flow.augmentBy`,
  {lit}`CLRS.Chapter26.Flow.augment`,
  {lit}`CLRS.Chapter26.Flow.augmentBy_value`, and
  {lit}`CLRS.Chapter26.Flow.value_lt_augment`.

* 26.2 Edmonds-Karp analysis (partial).
  Main declarations:
  {lit}`CLRS.Chapter26.ResidualPathLength`,
  {lit}`CLRS.Chapter26.IsShortestDist`,
  {lit}`CLRS.Chapter26.isShortestDist_self`,
  {lit}`CLRS.Chapter26.IsShortestDist.unique`,
  {lit}`CLRS.Chapter26.isShortestDist_triangle`, and
  {lit}`CLRS.Chapter26.ShortestAugmentingPath`.

* 26.3 Maximum bipartite matching (partial).
  Main declarations:
  {lit}`CLRS.Chapter26.BipartiteGraph`,
  {lit}`CLRS.Chapter26.Matching`,
  {lit}`CLRS.Chapter26.toFlowNetwork`,
  {lit}`CLRS.Chapter26.matchingToFlow_value`.

* Theorem 26.6, Max-Flow Min-Cut (partial).
  Main declarations:
  {lit}`CLRS.Chapter26.Flow.eq_cutCapacity_implies_maximal`.

## Current Shape

Section 26.1 defines a {lit}`FlowNetwork` as a capacity function {lit}`c : V → V → ℝ`
together with a distinguished source {lit}`s` and sink {lit}`t`.  A feasible
flow {lit}`Flow` satisfies capacity constraint, skew symmetry, and flow
conservation.  The section proves Lemma 26.5 (net flow across any cut equals
flow value) and the generic Ford-Fulkerson correctness theorem: if there is no
augmenting path in the residual network, the flow is maximal.

The Ford-Fulkerson augmentation module packages a concrete simple residual
source-to-sink path, proves that its bottleneck is positive, constructs the
resulting feasible augmented flow, and proves both its exact and strict value
increase.  The existing reachability predicate has not yet been converted to
this concrete path representation.

The Edmonds-Karp module defines residual path lengths and shortest residual
distances.  It proves the self-distance, uniqueness, and one-edge triangle
helpers, and bundles a shortest augmenting path.  The predecessor/prefix and
augmentation-edge bridges needed for Lemma 26.7 have not yet been proved.

Section 26.3 defines bipartite graphs, matchings, the unit-capacity reduction,
and a matching-induced flow function.  Its current theorem
{lit}`matchingToFlow_value` is conditional: it assumes that the caller already
has a feasible {lit}`Flow` whose function equals {lit}`matchingFlowFun`.  It
does not construct that feasible flow or prove the integral-flow converse.

The companion file `Section_26_6_MaxFlow_MinCut` proves one direction of the
Max-Flow Min-Cut Theorem: if `|f| = c(S,T)` for some cut, then `f` is maximal.
The converse and the full three-condition equivalence are deferred.

## Deferred Work

* Convert residual reachability to a concrete simple augmenting path, then use
  strict flow-value increase to complete the constructive Max-Flow Min-Cut
  converse/equivalence.
* Prove Lemma 26.7 using predecessor/prefix facts and a bridge characterizing
  residual edges introduced by augmentation.
* Implement BFS and the Edmonds-Karp loop, then prove the {lit}`O(VE²)` work
  bound.
* Construct feasible flows from matchings, prove the integral-flow converse,
  and derive the maximum-value statement of Theorem 26.12.

Sections 26.4 and 26.5 are deferred outside the current selected milestone.
-/

namespace CLRS
namespace Chapter26

end Chapter26
end CLRS
