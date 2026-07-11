# Chapter 23 Closure Audit

Date: 2026-07-11

Status: `main-proof-complete-for-correctness`

## Acceptance Boundary

The Chapter 23 seal covers the mathematical correctness claims for the cut
property, Kruskal's algorithm, and Prim's algorithm on the repository's finite
edge-labelled graph model.  It includes automatic tree-path exchange and
prefix-local sorted lightness.  It does not claim a stateful union-find scan, a
concrete priority queue, exact work bounds, mutable graph storage, RAM
semantics, exercises, or chapter-end problems.

Follow-up on 2026-07-11: the stateful union-find scan, concrete indexed Prim
queue, and algorithm-level work bounds have since been discharged by
`StatefulKruskal.lean` and `ExecutablePrim.lean`.  Mutable storage, concrete
`Batteries.BinaryHeap` array refinement, RAM charges, and exercises remain
outside this mathematical closure audit.

## Source Directory

| Section | Source | Responsibility |
| --- | --- | --- |
| 23.1 | `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean` | Finite graph and MST specifications, exchange kernel, cut property, safe edges |
| 23.2 | `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean` | Canonical tree paths, automatic exchange, sorted Kruskal, Prim traces and correctness |
| 23.2 refinement | `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/UnionFindBridge.lean` | Chapter 21 union-find refinement to the cycle-test interface |

## Closure Theorems

- `FiniteGraph.canonicalSimplePath_unique`: every connected pair in a selected
  forest has one simple path in the induced loop-free graph.
- `FiniteGraph.exists_crossing_exchangePath_of_spanningTree`: the canonical
  tree path automatically supplies a crossing replacement edge and
  `ExchangePath` witness.
- `FiniteGraph.cutCertificate_of_lightest_crossing_auto`: a finite light edge
  crossing a respecting cut is safe without a caller-supplied cycle exchange.
- `FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty`:
  a sorted complete exact-component Kruskal scan returns an MST, with local
  lightness and exchange generated inside the recursive proof.
- `FiniteGraph.prim_minimum_spanning_tree`: a complete certified Prim
  light-edge trace from the empty forest returns an MST.

## Requirement Audit

| Requirement | Evidence | Result |
| --- | --- | --- |
| Canonical finite-tree simple path | `selectedSimpleGraph_isAcyclic`, `canonicalSimplePath`, `canonicalSimplePath_unique` | Complete |
| Crossing cut edge with residual path decomposition | `exists_pathExchange_of_simplePath_crosses`, `exists_crossing_exchangePath_of_spanningTree` | Complete |
| Automatic Kruskal cycle exchange | `cutCertificate_of_lightest_crossing_auto`, `safeEdge_of_lightest_crossing_auto` | Complete |
| Prefix-local sorted lightness in recursive Kruskal | `cutCertificate_of_exactComponentKruskalPrefix_auto`, `kruskal_preserves_mst_of_sorted_exact_component` | Complete |
| End-to-end sorted Kruskal optimality | `kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty` | Complete |
| Prim correctness through the shared cut property | `PrimTrace`, `prim_preserves_mst`, `prim_spanning_tree_of_certificate`, `prim_minimum_spanning_tree` | Complete |

## Verification Evidence

- `lake build CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim`
- `lake env lean Tests/Chapter_23_Interface.lean`
- `lake env lean Tests/Chapter_23_Closure.lean`
- `lake env lean Tests/Chapter_23_UnionFind_Interface.lean`
- `uv run python scripts/check_repository.py`
- `lake build CLRSLean`
- `lake build :literateHtml`
- unfinished-proof marker scan over `CLRSLean/Chapter_23`

`Tests/Chapter_23_Closure.lean` prints the axiom dependencies of the four
closure theorems.  They use only `propext`, `Classical.choice`, and
`Quot.sound`, as expected for the noncomputable finite-set and quotient-based
simple-graph model; no project-specific axiom is introduced.

## Deferred Refinements

- Incremental stateful Kruskal execution connected to Chapter 21's costed
  union-find machine.
- A concrete priority queue and key-update implementation for Prim.
- Exact operation counts and asymptotic work packaging.
- Mutable graph storage and RAM semantics.
- Exercises and chapter-end problems.

These refinements may extend Chapter 23 without changing its sealed
mathematical-correctness status.
