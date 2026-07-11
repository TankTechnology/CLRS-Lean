import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.UnionFindBridge

/-!
# Chapter 23 - Minimum Spanning Trees

Chapter 23 formalizes the mathematical correctness stack for minimum spanning
trees: the cut property, canonical tree paths and exchange edges, end-to-end
Kruskal optimality, and Prim optimality.

## Sections

* 23.1 Growing a minimum spanning tree: {lit}`main-proof-complete-for-correctness`.
  Main results:
  {lit}`CLRS.MST.Graph.connected_crosses_cut`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`,
  and {lit}`CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: {lit}`main-proof-complete-for-correctness`.
  Closure results:
  {lit}`CLRS.MST.FiniteGraph.canonicalSimplePath_unique`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_exchangePath_of_spanningTree`,
  {lit}`CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing_auto`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty`,
  and {lit}`CLRS.MST.FiniteGraph.prim_minimum_spanning_tree`.

## Current Shape

Section 23.1 supplies the reusable cut-property kernel and concrete finite-graph
MST specification.  Section 23.2 proves that a selected forest induces an
acyclic simple graph with a unique canonical path.  A path crossing a cut
automatically yields the exchange edge and the two residual connections needed
by {lit}`ExchangePath`, eliminating the former manual cycle certificate.

Kruskal's proof now carries the processed prefix through the recursion, derives
local sorted lightness from exact components, constructs every exchange
certificate internally, and discharges the final spanning-tree condition for a
complete connected scan.  Prim is represented by a dynamic light-edge trace;
the shared cut property proves safe extension, exact components prove forest
preservation, and a complete trace returns a concrete minimum spanning tree.

## Deferred Work

The sealed boundary is mathematical correctness on the finite edge-labelled
graph model.  Stateful union-find threading, a concrete priority queue for
Prim, exact work bounds, and mutable/RAM refinements remain implementation
layers; they do not reopen the Chapter 23 correctness milestone.
-/
