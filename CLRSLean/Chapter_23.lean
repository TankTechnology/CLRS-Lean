import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# Chapter 23 - Minimum Spanning Trees

Chapter 23 tracks the minimum-spanning-tree proof stack.  The current focus is
the mathematical CLRS argument: safe edges, cut certificates, and Kruskal's
safe-edge induction.

## Sections

* 23.1 Growing a minimum spanning tree: `partial`.
  Main result: `CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: `partial`.
  Main results: `CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  `CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  `CLRS.MST.FiniteGraph.kruskal_spans_of_complete_exact_component`, and
  `CLRS.MST.kruskal_optimal`.

## Current Shape

Section 23.1 contains the cut-property core.  It proves that a light edge
crossing a cut is safe once the graph-specific exchange certificate is supplied.
The finite graph definitions, spanning-tree specification, and safe-edge
interface are already present.

Section 23.2 contains the sorted-order lightness layer, exact-component prefix
accounting, and a mathematical Kruskal skeleton.  It proves that an exact
component oracle accounts for every previously processed edge, derives the
processed-prefix exclusion invariant, and then uses sorted edge order to make
the current edge light.  For finite connected graphs with a complete edge scan,
it proves that the exact-component Kruskal output spans all vertices and
contains only graph edges.  It also proves that if every accepted edge carries a
safe-edge certificate and the final selected edge set is a spanning tree, then
the selected tree is optimal.

## Deferred Work

The project intentionally defers union-find correctness in the first phase.  The
mathematical proof should stabilize before adding an implementation refinement
for the cycle test.

The main strengthening targets are:

* refine exact components to an executable union-find implementation if that
  implementation proof becomes in scope;
* construct the concrete exchange edge automatically from finite graph paths;
* prove forest preservation for the component cycle test, then compose it with
  the existing subset and spanning theorems;
* add Prim's theorem interface after the Kruskal skeleton is complete.
-/
