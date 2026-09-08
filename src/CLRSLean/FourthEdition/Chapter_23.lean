import CLRSLean.Chapter_25
import CLRSLean.FourthEdition.Chapter_23.Section_23_1_All_Pairs_Model
import CLRSLean.FourthEdition.Chapter_23.Section_23_2_Floyd_Warshall
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm
import CLRSLean.FourthEdition.Chapter_23.Section_23_2_Floyd_Warshall.NegativeCycle
import CLRSLean.FourthEdition.Chapter_23.MatrixExecution.Reindex
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm.Execution

/-!
# Chapter 23 — All-Pairs Shortest Paths

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 23.1--23.3 are native fourth-edition sections (shortest paths and
matrix multiplication, the Floyd–Warshall algorithm, and Johnson's algorithm
for sparse graphs), imported directly from
[Section 23.1](CLRSLean/FourthEdition/Chapter_23/Section_23_1_All_Pairs_Model/),
[Section 23.2](CLRSLean/FourthEdition/Chapter_23/Section_23_2_Floyd_Warshall/),
and
[Section 23.3](CLRSLean/FourthEdition/Chapter_23/Section_23_3_Johnsons_Algorithm/).
The sections extend the fourth-edition weighted-graph model (Section 22.1).
Declarations retain the legacy {lit}`CLRS.Chapter24.WeightedGraph` namespace
during the compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_25` and {lit}`CLRSLean.Chapter_25.Section_25_*`
forward to these sources.

## Coverage boundary

The native sections prove valid-input shortest-path correctness. The legacy
matrix initializer sets the diagonal to zero and cannot detect a negative
self-edge. The cycle-safe initializer preserves those edges, and
{lit}`cycleFloydWarshall_negative_iff` proves that a negative final diagonal
is equivalent to a negative cycle, with no absence-of-negative-cycles premise.
Under {lit}`NoNegCycle`, the corrected and legacy distance results agree.

{lit}`MatrixExecution` stores each completed table, shares each previous
phase once, and counts actual min-plus scans and table writes. Its Floyd
updates are exactly {lit}`n³`; repeated squaring has exactly
{lit}`numSquarings * n³` candidate visits. Separate counters include initial
and intermediate table writes and the final {lit}`n` diagonal scan. An explicit
vertex/index equivalence supports arbitrary finite carriers. These are exact
real-arithmetic cell models, excluding enumeration construction, allocation and
bit costs; the real comparisons remain noncomputable primitives in Lean.

Johnson's existing construction assumes {lit}`NoNegCycle` and has no
negative-cycle failure result. Its heap expression is a conditional backend
budget. The separate {lit}`JohnsonExecution.johnsonStored` over indexed
graphs {lit}`Fin n` prepares a stored Bellman–Ford potential, caches reweighted
edges, runs a stored scan queue from each source and retains every result row.
Its actual counter is at most {lit}`4n³ + 14n² + 12n + 4`, hence
{lit}`16(n+1)³`. It refines the original valid-input Johnson distances. Graph
queries, indexed access and real arithmetic are primitives; finite-set lookup
internals, persistent-array copying and bit costs are not included.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
