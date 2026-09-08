# Chapter 35 Repair Record

Issue [#375](https://github.com/TankTechnology/CLRS-Lean/issues/375) was resolved.

- `TSP.GraphAdapter.graphTour` starts from a finite natural-weight graph and root,
  runs the Chapter 21 Prim frontier construction, roots selected edges, and proves
  the two-approximation theorem without caller-supplied MST or parent adapters.
- Set-cover theorems attach both approximation bounds to the cardinality of the
  family returned by the actual greedy execution.
- `RandomizedLP.VertexCoverLP.program` constructs edge and box constraints, calls
  the Chapter 29 solver contract, retains an optimal solution, and proves that
  half-threshold rounding returns a cover within twice every competitor's weight.
- MAX-3-CNF is explicitly an unweighted `Finset` model with three distinct
  variables per clause. The completed SUBSET-SUM FPTAS execution count is exposed.

The LP composition uses exact real semantics and does not claim rational
computability, polynomial-time SIMPLEX, numerical stability, or bit complexity.
Focused graph, set-cover, LP, self-loop, zero-weight, and empty-domain tests passed,
as did all new public axiom checks.
