# CLRS-lean Proof Map

This ledger records what is proved, what is partial, and what is currently
deferred.  It is intended to become the website's main navigation table.

## Chapter 16 - Greedy Algorithms

### Section 16.3 - Huffman codes

- Lean source: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`
- Status: `proved`
- Main theorem: `HuffmanV2.optimum_huffman_freqs`
- Proof pattern: greedy exchange argument, split-leaf transformation
- Current gap: none for the current theorem statement

The section proves that Huffman coding produces an optimal prefix tree for a
nonempty frequency table with distinct symbols and positive frequencies.

## Chapter 23 - Minimum Spanning Trees

### Section 23.1 - Growing a minimum spanning tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.safe_edge_of_lightest_crossing`
- Supporting theorem: `CLRS.MST.mst_exchange_step`
- Proof pattern: cut property, safe edge, exchange argument
- Current gap: the concrete path/cycle lemma that constructs the exchange edge
  from a finite graph spanning tree is still an explicit certificate.

This section contains the mathematical core of the CLRS MST proof.  It proves
that a light edge crossing a cut is safe once the graph-specific exchange
certificate is supplied.

### Section 23.2 - Kruskal and Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.kruskal_optimal`
- Supporting theorem: `CLRS.MST.FiniteGraph.kruskal_optimal`
- Proof pattern: safe-edge induction over an edge list
- Deferred implementation: union-find correctness
- Current gaps:
  - derive lightness automatically from a sorted edge order;
  - prove the final selected edge set is a spanning tree from connectedness and
    complete edge scan;
  - add Prim's algorithm theorem interface.

The section currently proves a mathematical Kruskal skeleton: if accepted edges
come with safe-edge certificates and the final selected set is a spanning tree,
then the result is optimal.

## Deferred And Blocked Items

| Item | Status | Reason |
| --- | --- | --- |
| Union-find implementation correctness | `deferred-implementation` | Not needed for the mathematical MST correctness theorem. |
| Sorted-order lightness for Kruskal | `partial` | Needs a list-order invariant over processed edges. |
| Concrete MST exchange edge from paths | `blocked-design` | Needs a stable finite path/walk representation. |
| Prim's algorithm | `statement` | Section file exists only through the Chapter 23.2 target; theorem interface has not been added yet. |

## Publication Value

The proof map is intentionally honest.  Completed sections show theorem names
that compile.  Partial sections expose the exact missing mathematical or
representation layer.  This lets future contributors pick a section without
reverse-engineering the project state.
