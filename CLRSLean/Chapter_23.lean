import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.UnionFindBridge

/-!
# Chapter 23 - Minimum Spanning Trees

Chapter 23 tracks the minimum-spanning-tree proof stack.  The current focus is
the mathematical CLRS argument: safe edges, cut certificates, and Kruskal's
safe-edge induction.

## Sections

* 23.1 Growing a minimum spanning tree: {lit}`partial`.
  Main results:
  {lit}`CLRS.MST.Graph.connected_crosses_cut`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`,
  and {lit}`CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: {lit}`partial`.
  Main results: {lit}`CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  {lit}`CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  {lit}`CLRS.MST.Graph.ExchangePath`,
  {lit}`CLRS.MST.Graph.InsertedEdgeConnection`,
  {lit}`CLRS.MST.Graph.exchangePath_connected_insert`,
  {lit}`CLRS.MST.Graph.insertedEdgeConnection_of_exchangePath`,
  {lit}`CLRS.MST.Graph.exchangePath_of_insert_connected`,
  {lit}`CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`,
  {lit}`CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`,
  {lit}`CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`,
  {lit}`CLRS.MST.FiniteGraph.spanningTree_exchange_of_path_certificate`,
  {lit}`CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_optimal_of_complete_exact_component_empty`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_cycle_test`,
  {lit}`CLRS.MST.UnionFindConnectivityRefinement.checkEquiv_iff_connected`,
  {lit}`CLRS.MST.UnionFindConnectivityRefinement.cycleTest_correct`,
  and
  {lit}`CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_complete_exact_component_empty`.

## Current Shape

Section 23.1 contains the cut-property core.  It proves that a light edge
crossing a cut is safe once the graph-specific exchange certificate is supplied.
The finite graph definitions, spanning-tree specification, safe-edge interface,
empty-prefix MST equivalence, and path/cut crossing-edge lemma are already
present.

Section 23.2 contains the sorted-order lightness layer, exact-component prefix
accounting, and a mathematical Kruskal skeleton.  It proves that an exact
component oracle accounts for every previously processed edge, derives the
processed-prefix exclusion invariant, and then uses sorted edge order to make
the current edge light.  It also contains the certificate-based replacement
exchange theorem: an explicit {lit}`ExchangePath` certificate proves that
adding the accepted edge and deleting one tree edge preserves the spanning-tree
property.  The path bridge now goes both ways between an inserted-edge
connection across the erased tree edge and the reusable {lit}`ExchangePath`
certificate, leaving only the canonical finite path/cycle extraction layer as
future work.  For finite connected graphs with a complete edge scan, it proves that
an exact-component Kruskal pass preserves forests and returns a spanning tree
from an initial forest.  It also proves finite-graph optimality wrappers,
including direct concrete minimum-spanning-tree theorems for both a complete
exact-component scan and an abstract cycle-test implementation once its final
accepted edge set is known to be a spanning tree.

## Deferred Work

Chapter 21 now supplies executable union-find functional correctness, and the
nested union-find bridge refines its equivalence query to this chapter's cycle-
test interface.  The bridge currently takes an extensional state family indexed
by the selected edge set; a mutable/stateful Kruskal scan remains a lower-level
performance refinement.

The main strengthening targets are:

* refine the extensional union-find state family to an incremental stateful
  Kruskal scan with an explicit operation-cost semantics;
* derive the inserted-edge connection automatically from a canonical finite
  simple path/cycle representation;
* discharge prefix-local sorted lightness inside the full recursive optimality
  wrapper, rather than requiring a global lightness hypothesis;
* add Prim's theorem interface after the Kruskal skeleton is complete.
-/
