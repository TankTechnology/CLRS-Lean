import CLRSLean.Chapter_24
import CLRSLean.FourthEdition.Chapter_22.Section_22_1_Bellman_Ford
import CLRSLean.FourthEdition.Chapter_22.Section_22_2_SSSP_In_DAGs
import CLRSLean.FourthEdition.Chapter_22.Section_22_3_Dijkstra
import CLRSLean.FourthEdition.Chapter_22.Section_22_4_Difference_Constraints
import CLRSLean.FourthEdition.Chapter_22.Section_22_5_Shortest_Path_Properties
import CLRSLean.FourthEdition.Chapter_22.Section_22_5_Shortest_Path_Properties.PredecessorTree

/-!
# Chapter 22 — Single-Source Shortest Paths

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 22.1--22.5 are native fourth-edition sections (Bellman–Ford, SSSP
in DAGs, Dijkstra, difference constraints, and the shortest-path property
proofs), imported directly from
[Section 22.1](CLRSLean/FourthEdition/Chapter_22/Section_22_1_Bellman_Ford/),
[Section 22.2](CLRSLean/FourthEdition/Chapter_22/Section_22_2_SSSP_In_DAGs/),
[Section 22.3](CLRSLean/FourthEdition/Chapter_22/Section_22_3_Dijkstra/),
[Section 22.4](CLRSLean/FourthEdition/Chapter_22/Section_22_4_Difference_Constraints/),
and
[Section 22.5](CLRSLean/FourthEdition/Chapter_22/Section_22_5_Shortest_Path_Properties/).
Declarations retain the legacy `CLRS.Chapter24` namespace during the
compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_24` and {lit}`CLRSLean.Chapter_24.Section_24_*` forward
to these sources.

## Coverage boundary

Bellman–Ford proves synchronous distance correctness under global
{lit}`NoNegCycle`; it does not return failure for source-reachable negative
cycles or weaken the premise to source-relative absence. DAG shortest paths
require a supplied complete topological order. Dijkstra proves its mathematical
loop under nonnegative edge weights; its binary-heap budget is an independent
backend formula, not a measured concrete priority-queue execution. The
vertex/edge and round/edge formulas likewise do not imply stored-table reuse.

Difference constraints use a fresh source reaching every variable, so global
negative-cycle absence is appropriate for their feasibility equivalence.
The old independently minimizing predecessor selector proves tight edges only;
zero-weight cycles show why a separate decreasing-depth parent construction
is required for a source-rooted shortest-path tree. The new {lit}`shortestPathTree`
computes distances, constructs the tight-edge graph, and returns its actual BFS
parents and depths. {lit}`shortestPathTree_correct` proves source-rooted weighted
shortest paths and coverage; strictly decreasing depths prove acyclicity even
with zero-weight cycles. This classical construction adds no runtime claim.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
