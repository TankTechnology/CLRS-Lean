import CLRSLean.Chapter_16
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching

/-!
# Chapter 15 — Greedy Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_16`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

Section 15.4 (offline caching) is a native fourth-edition section (the
farthest-in-future eviction policy; the optimality theorem remains a gap),
imported through
[Section 15.4](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/).
The section is split into the sub-modules:

* [Cache Model](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S1_Cache_Model/)
* [Farthest-In-Future Eviction](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S2_Farthest_In_Future/)
* [Optimality](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S3_Optimality/)
The remaining sections reuse the legacy greedy-algorithms source through the
compatibility facade.  The third-edition Chapter

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
