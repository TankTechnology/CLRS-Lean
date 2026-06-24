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
  Main results: `CLRS.MST.lightest_crossing_of_sorted_prefix` and
  `CLRS.MST.kruskal_optimal`.

## Current Shape

Section 23.1 contains the cut-property core.  It proves that a light edge
crossing a cut is safe once the graph-specific exchange certificate is supplied.
The finite graph definitions, spanning-tree specification, and safe-edge
interface are already present.

Section 23.2 contains the sorted-order lightness layer and a mathematical
Kruskal skeleton.  It proves that sorted edge order makes the current edge light
once the processed prefix is known not to cross the current cut.  It also proves
that if every accepted edge carries a safe-edge certificate and the final
selected edge set is a spanning tree, then the selected tree is optimal.

## Deferred Work

The project intentionally defers union-find correctness in the first phase.  The
mathematical proof should stabilize before adding an implementation refinement
for the cycle test.

The main strengthening targets are:

* derive the cut certificate automatically when Kruskal accepts an edge;
* derive the processed-prefix exclusion invariant from an exact cycle-test or
  component model;
* prove the final accepted edge set is a spanning tree under the usual
  connected-graph and complete-edge-list assumptions;
* add Prim's theorem interface after the Kruskal skeleton is complete.
-/
