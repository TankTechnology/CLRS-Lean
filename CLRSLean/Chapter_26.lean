import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

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

## Current Shape

Section 26.1 defines a {lit}`FlowNetwork` as a capacity function {lit}`c : V → V → ℝ`
together with a distinguished source {lit}`s` and sink {lit}`t`.  A feasible
flow {lit}`Flow` satisfies capacity constraint, skew symmetry, and flow
conservation.  The section proves Lemma 26.5 (net flow across any cut equals
flow value) and the generic Ford-Fulkerson correctness theorem: if there is no
augmenting path in the residual network, the flow is maximal.

## Deferred Work

* The full Max-Flow Min-Cut Theorem (the converse direction).
* The specific Edmonds-Karp analysis (Section 26.2).
* Executable augmenting-path search and the augmenting loop.
-/

namespace CLRS
namespace Chapter26

end Chapter26
end CLRS
