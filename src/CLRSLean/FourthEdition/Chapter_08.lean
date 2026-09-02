import CLRSLean.FourthEdition.Chapter_08.Section_08_1_Lower_Bound_For_Sorting
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.CountTables
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray
import CLRSLean.FourthEdition.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Chapter 8 — Sorting in Linear Time

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 8.1--8.4 are native fourth-edition sections (lower bounds for sorting,
counting sort, radix sort, and bucket sort), imported directly from
[Section 8.1](CLRSLean/FourthEdition/Chapter_08/Section_08_1_Lower_Bound_For_Sorting/),
[Section 8.2](CLRSLean/FourthEdition/Chapter_08/Section_08_2_Counting_Sort/),
[Section 8.3](CLRSLean/FourthEdition/Chapter_08/Section_08_3_Radix_Sort/), and
[Section 8.4](CLRSLean/FourthEdition/Chapter_08/Section_08_4_Bucket_Sort/).
Section 8.2 includes the nested count-table and mutable output-array
refinements.  Declarations retain the `CLRS.Chapter08` namespace during the
compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_08` and {lit}`CLRSLean.Chapter_08.Section_08_*` forward
to these sources.

## Coverage boundary

The represented lower-bound and linear-time sorting developments are reused.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
