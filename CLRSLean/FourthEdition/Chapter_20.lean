import CLRSLean.Chapter_22
import CLRSLean.FourthEdition.Chapter_20.Section_20_1_Representing_Graphs
import CLRSLean.FourthEdition.Chapter_20.Section_20_2_BFS
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS.S1_WhitePath
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS.S2_Intervals
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS.S3_Bridge
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS.S4_SCC
import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS.S5_EdgeClassification
import CLRSLean.FourthEdition.Chapter_20.Section_20_4_Topological_Sort
import CLRSLean.FourthEdition.Chapter_20.Section_20_5_Strongly_Connected_Components
import CLRSLean.FourthEdition.Chapter_20.Section_20_5_Strongly_Connected_Components.MergeSortCongr

/-!
# Chapter 20 — Elementary Graph Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 20.1--20.5 are native fourth-edition sections (representing
graphs, breadth-first search, depth-first search with its nested
white-path/intervals/bridge/SCC/edge-classification developments,
topological sort, and strongly connected components), imported directly
from
[Section 20.1](CLRSLean/FourthEdition/Chapter_20/Section_20_1_Representing_Graphs/),
[Section 20.2](CLRSLean/FourthEdition/Chapter_20/Section_20_2_BFS/),
[Section 20.3](CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/),
[Section 20.4](CLRSLean/FourthEdition/Chapter_20/Section_20_4_Topological_Sort/),
and
[Section 20.5](CLRSLean/FourthEdition/Chapter_20/Section_20_5_Strongly_Connected_Components/).
Declarations retain the legacy `CLRS.Chapter22` namespace during the
compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_22` and {lit}`CLRSLean.Chapter_22.Section_22_*` forward
to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [White-Path Theorem](CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S1_WhitePath/)
* [Intervals and Timestamps](CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S2_Intervals/)
* [Discovery-State Bridge](CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S3_Bridge/)
* [SCC Preliminaries](CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S4_SCC/)
* [Edge Classification](CLRSLean/FourthEdition/Chapter_20/Section_20_3_DFS/S5_EdgeClassification/)
* [Merge-Sort Congruence](CLRSLean/FourthEdition/Chapter_20/Section_20_5_Strongly_Connected_Components/MergeSortCongr/)

## Coverage boundary

The native sections supply all represented fourth-edition elementary-graph
sections.  The namespace migration `CLRS.Chapter22` → `CLRS.Chapter20` is
tracked chapter by chapter.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
