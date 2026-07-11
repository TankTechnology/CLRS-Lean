import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.UnionFindBridge
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.StatefulKruskal
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.ExecutablePrim

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

The implementation layer now threads the real Chapter 21 costed union-find
machine through Kruskal, proves its connectivity invariant at every edge, and
identifies its output with mathematical Kruskal.  It composes sorting, scan,
and union-find work into explicit `O(E log E)` and `O((E+V) alpha(V))` bounds.
The executable Prim layer supplies indexed queue membership, `key`, `parent`,
`decreaseKey`, and `extractMin`; a concrete frontier provider refines its edge
choices to `PrimTrace`.  The binary-heap operation model proves
`O((E+V) log V)`, hence `O(E log V)` for connected nontrivial graphs, and also
records unsorted-array and Fibonacci-heap alternatives.

## Deferred Work

The sealed boundary now includes functional implementation refinements and
algorithm-level work bounds.  Remaining work is the semantic refinement from
the indexed queue contract to the concrete `Batteries.BinaryHeap` array state,
plus mutable-array/RAM write accounting.  These do not reopen the Chapter 23
correctness milestone.
-/
