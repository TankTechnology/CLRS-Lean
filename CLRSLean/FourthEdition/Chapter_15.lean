import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection
import CLRSLean.FourthEdition.Chapter_15.Section_15_2_Greedy_Meta
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching

/-!
# Chapter 15 — Greedy Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 15.1--15.3 are native fourth-edition sections (activity selection,
the greedy-choice/optimal-substructure meta-theorems, and Huffman codes),
imported directly from
[Section 15.1](CLRSLean/FourthEdition/Chapter_15/Section_15_1_Activity_Selection/),
[Section 15.2](CLRSLean/FourthEdition/Chapter_15/Section_15_2_Greedy_Meta/),
and
[Section 15.3](CLRSLean/FourthEdition/Chapter_15/Section_15_3_Huffman_Codes/).
Declarations keep their legacy namespaces (`CLRS.ActivitySelection`,
`CLRS.GreedyMeta`, `CLRS.HuffmanV2`); the third-edition-numbered imports
{lit}`CLRSLean.Chapter_16` and {lit}`CLRSLean.Chapter_16.Section_16_*` forward to
these sources during the compatibility period.

## Coverage boundary

Section 15.4 (offline caching) is a native fourth-edition section (the
farthest-in-future eviction policy; the optimality theorem remains a gap),
imported through
[Section 15.4](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/).
The section is split into the sub-modules:

* [Cache Model](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S1_Cache_Model/)
* [Farthest-In-Future Eviction](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S2_Farthest_In_Future/)
* [Optimality](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S3_Optimality/)

The third-edition Sections 16.4 (matroids) and 16.5 (task scheduling) are
retained as supplementary online material (reachable through
{lit}`CLRSLean.OnlineMaterial`).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
