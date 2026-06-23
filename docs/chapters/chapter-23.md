# Chapter 23 - Minimum Spanning Trees

## Section 23.1 - Growing A Minimum Spanning Tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main theorem: `CLRS.MST.safe_edge_of_lightest_crossing`

This section contains the cut-property core.  It proves the safe-edge theorem
from a bundled cut certificate.  The remaining work is the concrete graph lemma
that constructs the exchange edge from a spanning-tree path or cycle.

## Section 23.2 - Kruskal And Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main theorem: `CLRS.MST.kruskal_optimal`

The current Kruskal proof is mathematical rather than implementation-level.  It
uses an abstract cycle test and safe-edge certificates.  Union-find correctness
is intentionally deferred.

Open tasks:

- prove sorted edge order implies the accepted edge is light across its cut;
- prove the final Kruskal output is a spanning tree under the usual connected
  graph and complete edge list assumptions;
- add the Prim theorem interface after Kruskal's mathematical version is stable.
