import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.S1_UnionFindBridge
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.S2_StatefulKruskal
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.S3_ExecutablePrim

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

The implementation layer threads the actual costed union-find machine through
Kruskal and proves connectivity/output refinement. Its combined work expression
adds an independent sorting budget to the scan and union-find counters.

The canonical fourth-edition Chapter 21 imports completion proofs for the
frontier run and a cached array Prim execution. The latter constructs its own
MST and counts queue/index preparation, array reads/writes, key comparisons
and adjacency visits, with a {lit}`2n² + 5n + 6E` bound. The existing binary-heap
formula is conditional on backend operations; it is not the cost of the
reference frontier rescan or an implemented binary heap. The new array variant
supplies its own concrete queue proof. Allocation and bit costs remain outside
these abstract operation models.
-/
