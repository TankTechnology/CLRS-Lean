import CLRSLean.Chapter_24
import CLRSLean.FourthEdition.Chapter_22.Section_22_1_Bellman_Ford
import CLRSLean.FourthEdition.Chapter_22.Section_22_2_SSSP_In_DAGs
import CLRSLean.FourthEdition.Chapter_22.Section_22_3_Dijkstra
import CLRSLean.FourthEdition.Chapter_22.Section_22_4_Difference_Constraints
import CLRSLean.FourthEdition.Chapter_22.Section_22_5_Shortest_Path_Properties

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

The native sections supply the represented fourth-edition
single-source-shortest-path sections (CLRS Theorem 22.4 / Lemmas 22.11--22.13
and Theorem 22.9 for difference constraints).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
