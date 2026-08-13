import CLRSLean.Chapter_23
import CLRSLean.FourthEdition.Chapter_21.Section_21_1_Growing_Minimum_Spanning_Trees
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S1_UnionFindBridge
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S2_StatefulKruskal
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S3_ExecutablePrim

/-!
# Chapter 21 — Minimum Spanning Trees

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 21.1--21.2 are native fourth-edition sections (growing a minimum
spanning tree, and Kruskal and Prim with the nested union-find bridge,
incremental costed Kruskal, and executable indexed-queue Prim
developments), imported directly from
[Section 21.1](CLRSLean/FourthEdition/Chapter_21/Section_21_1_Growing_Minimum_Spanning_Trees/)
and
[Section 21.2](CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/).
The Kruskal bridge imports the fourth-edition disjoint-set sources
(Chapter 19).  Declarations retain the legacy `CLRS.MST` namespace during
the compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_23` and {lit}`CLRSLean.Chapter_23.Section_23_*` forward
to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Union-Find Refinement](CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/S1_UnionFindBridge/)
* [Stateful Kruskal](CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/S2_StatefulKruskal/)
* [Executable Prim](CLRSLean/FourthEdition/Chapter_21/Section_21_2_Kruskal_And_Prim/S3_ExecutablePrim/)

## Coverage boundary

The native sections supply the represented fourth-edition
minimum-spanning-tree sections (Theorem 21.1 safe-edge characterization
and the Kruskal/Prim correctness chains).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
