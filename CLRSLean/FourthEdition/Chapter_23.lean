import CLRSLean.FourthEdition.Chapter_23.Section_23_1_All_Pairs_Model
import CLRSLean.FourthEdition.Chapter_23.Section_23_2_Floyd_Warshall
import CLRSLean.FourthEdition.Chapter_23.Section_23_3_Johnsons_Algorithm

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

The native sections supply the represented fourth-edition all-pairs
shortest-path sections (Lemmas 23.1--23.2 and 23.7, Theorems 23.3, 23.5 and
23.8).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
