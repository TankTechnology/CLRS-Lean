# Chapter 23 - Minimum Spanning Trees

## Section 23.1 - Growing A Minimum Spanning Tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `main-proof-complete-for-correctness`
- Main theorems:
  `CLRS.MST.Graph.connected_crosses_cut`,
  `CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  `CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  `CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`, and
  `CLRS.MST.safe_edge_of_lightest_crossing`

This section contains the cut-property core.  It proves the safe-edge theorem
from a bundled cut certificate and now derives a crossing tree edge from the
spanning-tree path between the endpoints of a cut-crossing edge.  It also proves
that the abstract empty-prefix `IsMSTExtending` specification is equivalent to
the concrete finite-graph `IsMinimumSpanningTree` specification.

## Section 23.2 - Kruskal And Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Implementation sources:
  `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/S2_StatefulKruskal.lean` and
  `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/S3_ExecutablePrim.lean`
- Status: `main-proof-complete-for-correctness`
- Main theorems:
  `CLRS.MST.Graph.ExchangePath`,
  `CLRS.MST.Graph.InsertedEdgeConnection`,
  `CLRS.MST.Graph.exchangePath_connected_insert`,
  `CLRS.MST.Graph.insertedEdgeConnection_of_exchangePath`,
  `CLRS.MST.Graph.exchangePath_of_insert_connected`,
  `CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`,
  `CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`,
  `CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`,
  `CLRS.MST.FiniteGraph.spanningTree_exchange_of_path_certificate`,
  `CLRS.MST.FiniteGraph.exists_replacement_spanning_tree_of_cut`,
  `CLRS.MST.FiniteGraph.canonicalSimplePath_unique`,
  `CLRS.MST.FiniteGraph.exists_crossing_exchangePath_of_spanningTree`,
  `CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing_auto`,
  `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty`,
  `CLRS.MST.FiniteGraph.prim_minimum_spanning_tree`,
  `CLRS.MST.StatefulKruskal.scan_initial_selected_eq_kruskal`,
  `CLRS.MST.StatefulKruskal.scan_initial_cost_le_inverseAckermann`,
  `CLRS.MST.StatefulKruskal.totalWork_le_forty_mul_edge_log`,
  `CLRS.MST.ExecutablePrim.frontierRun_refines_PrimTrace`, and
  `CLRS.MST.ExecutablePrim.binaryHeapWork_le_edge_log`

The selected-forest view is proved acyclic, so its chosen simple path is unique.
When that path crosses a cut, Lean extracts the crossing tree edge together
with the residual prefix and suffix connections, automatically constructing
the `ExchangePath` and cut certificate used by the safe-edge theorem.

The sorted Kruskal proof carries its processed prefix through the recursion,
derives local lightness from exact components, constructs exchange witnesses
internally, and returns a concrete MST for a complete connected scan.  Prim is
represented by a dynamic trace of light edges crossing the current root
component; the same cut-property stack proves safe extension, forest
preservation, spanning-tree correctness, and the final MST theorem.

The implementation layer now uses the real Chapter 21 costed union-find
machine for every Kruskal edge.  Its inductive invariant identifies
union-find classes with connectivity in the selected forest, its selected set
is equal to mathematical Kruskal, and its exact Chapter 21 operation trace
charges at most `18 * (E + V) * alpha(V)` for the executable cycle query plus
union.  Adding comparison sorting and linear scanning gives an explicit
`40 * E * (log2 E + 1)` textbook bound under
the standard `V <= E` and `alpha(V) <= log2 E + 1` conditions.

Executable Prim now has queue membership, finite/infinity keys, parent edges,
`decreaseKey`, and `extractMin`.  The concrete frontier provider builds these
keys from crossing graph edges and its run is proved to refine `PrimTrace`.
The binary-heap operation model gives `(2E + V)(log2 V + 1)`, hence at most
`4E(log2 V + 1)` for connected nontrivial graphs.  The remaining low-level
item is a semantic refinement of this indexed queue to the array representation
inside `Batteries.BinaryHeap`, together with mutable/RAM write charges.
