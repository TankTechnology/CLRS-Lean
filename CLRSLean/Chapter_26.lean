import CLRSLean.Chapter_26.Section_26_1_Flow_Networks
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.Ford_Fulkerson_Augmentation
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S2_EK_Loop
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S3_WorkAnalysis
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S4_ExecutableBFS
import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.Chapter_26.Section_26_4_Push_Relabel
import CLRSLean.Chapter_26.Section_26_5_Relabel_To_Front
import CLRSLean.Chapter_26.Section_26_6_MaxFlow_MinCut

/-! # Chapter 26 - Maximum Flow

Chapter 26 opens the maximum-flow part of the CLRS graph track.  The current
partial development builds a finite capacity-function model, proves concrete
Ford--Fulkerson augmentation and the full Max-Flow Min-Cut equivalence, and
exposes infrastructure for the later algorithms.

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
  {lit}`CLRS.Chapter26.Flow.maximal_of_noAugmentingPath`, and
  {lit}`CLRS.Chapter26.Flow.exists_cut_value_eq_of_noAugmentingPath`.

* 26.2 Ford-Fulkerson augmentation.
  Main declarations:
  {lit}`CLRS.Chapter26.Flow.ResidualPath`,
  {lit}`CLRS.Chapter26.Flow.AugmentingPath`,
  {lit}`CLRS.Chapter26.Flow.AugmentingPath.bottleneck`,
  {lit}`CLRS.Chapter26.Flow.augmentBy`,
  {lit}`CLRS.Chapter26.Flow.augment`,
  {lit}`CLRS.Chapter26.Flow.augmentBy_value`,
  {lit}`CLRS.Chapter26.Flow.augment_value`,
  {lit}`CLRS.Chapter26.Flow.value_lt_augment`,
  {lit}`CLRS.Chapter26.Flow.hasAugmentingPath_iff_nonempty_augmentingPath`, and
  {lit}`CLRS.Chapter26.Flow.not_maximal_of_hasAugmentingPath`.

* 26.2 Edmonds-Karp analysis.
  Main declarations:
  {lit}`CLRS.Chapter26.ResidualPathLength`,
  {lit}`CLRS.Chapter26.IsShortestDist`,
  {lit}`CLRS.Chapter26.isShortestDist_self`,
  {lit}`CLRS.Chapter26.IsShortestDist.unique`,
  {lit}`CLRS.Chapter26.isShortestDist_triangle`,
  {lit}`CLRS.Chapter26.IsShortestDist.exists_predecessor`,
  {lit}`CLRS.Chapter26.ShortestAugmentingPath`,
  {lit}`CLRS.Chapter26.ShortestAugmentingPath.shortest_prefix`,
  {lit}`CLRS.Chapter26.ShortestAugmentingPath.exists_shortestDist_le_augment`,
  and {lit}`CLRS.Chapter26.shortest_path_nondec` (Lemma 26.7).

* 26.3 Maximum bipartite matching.
  Main declarations:
  {lit}`CLRS.Chapter26.BipartiteGraph`,
  {lit}`CLRS.Chapter26.Matching`,
  {lit}`CLRS.Chapter26.toFlowNetwork`,
  {lit}`CLRS.Chapter26.matchingToFlow`,
  {lit}`CLRS.Chapter26.matchingToFlow_value`,
  {lit}`CLRS.Chapter26.matchingOfIntegralFlow`,
  {lit}`CLRS.Chapter26.matchingOfIntegralFlow_size`, and
  {lit}`CLRS.Chapter26.maxMatching_eq_maxFlow_value`
  (Theorem 26.12).

* 26.4 Push-relabel algorithms.
  Main declarations:
  {lit}`CLRS.Chapter26.Preflow`,
  {lit}`CLRS.Chapter26.Preflow.excess`,
  {lit}`CLRS.Chapter26.Preflow.isOverflowing`,
  {lit}`CLRS.Chapter26.IsValidHeight`,
  {lit}`CLRS.Chapter26.admissibleEdge`,
  {lit}`CLRS.Chapter26.Preflow.pushBy`,
  {lit}`CLRS.Chapter26.Preflow.push`,
  {lit}`CLRS.Chapter26.relabel`,
  {lit}`CLRS.Chapter26.height_le_of_overflowing` (Lemma 26.15), and
  {lit}`CLRS.Chapter26.maximal_of_no_overflow`.

* Theorem 26.6, Max-Flow Min-Cut.
  Main declarations:
  {lit}`CLRS.Chapter26.Flow.eq_cutCapacity_implies_maximal`,
  {lit}`CLRS.Chapter26.Flow.maximal_iff_noAugmentingPath`, and
  {lit}`CLRS.Chapter26.Flow.maximal_iff_exists_cut_value_eq`.

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
increase.  It also converts residual source-to-sink reachability to this
concrete simple-path representation and uses augmentation to prove that any
flow with an augmenting path is not maximal.

The Edmonds-Karp module defines residual path lengths and shortest residual
distances.  It proves predecessor and shortest-prefix facts, characterizes the
new residual edges introduced by augmentation, and combines those bridges into
the monotonic residual-distance theorem of Lemma 26.7.  The companion
submodules assemble the explicit shortest augmenting path from residual
reachability, run the Edmonds-Karp loop to an integral maximal flow
({lit}`edmondsKarp_maximal`), prove the critical-edge counting argument that
bounds the number of augmentations by `O(VE²)`
({lit}`critical_count_bound`, {lit}`augmentation_count_bound`), and supply an
executable breadth-first search ({lit}`residualBFS`) whose parent chain yields
the shortest augmenting path ({lit}`bfs_shortestAugmenting`).

Section 26.3 defines bipartite graphs, matchings, and the unit-capacity
reduction.  It constructs the feasible flow induced by every matching
({lit}`matchingToFlow`) with value equal to its size, recovers a matching of
size `v` from every integral flow of value `v` ({lit}`matchingOfIntegralFlow`),
and iterates shortest-free augmentation from the zero flow to obtain an
integral maximum flow.  These pieces combine into CLRS Theorem 26.12
({lit}`maxMatching_eq_maxFlow_value`): the maximum matching size equals the
maximum flow value.

The companion file `Section_26_6_MaxFlow_MinCut` proves the full Max-Flow
Min-Cut Theorem: maximality is equivalent both to the absence of a residual
source-to-sink path and to equality with the capacity of some cut.

Section 26.4 (push-relabel) formalizes the preflow-push model: a
{lit}`Preflow` relaxes conservation to nonnegative excess off the source, a
valid height function ({lit}`IsValidHeight`) bounds residual-edge height drops
by one, and the {lit}`Preflow.pushBy` and {lit}`relabel` operations preserve
both invariants.  The overflowing-vertex source-reachability lemma and the
`2|V| - 1` height bound ({lit}`height_le_of_overflowing`, Lemma 26.15) supply
the termination foundation, and {lit}`maximal_of_no_overflow` combines a valid
height function with zero internal excess to certify maximality via the
max-flow min-cut theorem.

## Deferred Work

Section 26.5 (relabel-to-front) and the fine-grained saturating/nonsaturating
push count (`O(V²E)`/`O(V³)`) are deferred outside the current selected
milestone.
-/

namespace CLRS
namespace Chapter26

end Chapter26
end CLRS
