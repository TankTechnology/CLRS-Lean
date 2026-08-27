import CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.FourthEdition.Chapter_02.Section_02_2_Analyzing_Algorithms
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge_Sort_Recurrence

/-!
# Chapter 2 — Getting Started

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 2.1--2.3 are native fourth-edition sections (insertion sort, analyzing
algorithms, and designing algorithms), imported directly from
[Section 2.1](CLRSLean/FourthEdition/Chapter_02/Section_02_1_Insertion_Sort/),
[Section 2.2](CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms/),
and
[Section 2.3](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/).
Section 2.2 includes the full symbolic insertion-sort line-cost table and its
best/worst trace specializations.  Section 2.3 includes the explicit costed
MERGE development, an executable recursive merge sort built from that MERGE,
and execution-derived recurrence and asymptotic results.
Declarations retain the `CLRS.Chapter02` namespace during the compatibility period; the
third-edition-numbered imports {lit}`CLRSLean.Chapter_02` and
{lit}`CLRSLean.Chapter_02.Section_02_*` forward to these sources.

## Coverage boundary

Insertion sort and merge sort use immutable lists.  Section 2.2's
line costs are the textbook symbolic unit-cost model, not operational word-RAM
semantics.  Section 2.3 proves the executable recursive merge sort correct,
identifies it with the compatibility API, and derives its all-input
{lit}`Theta(n log n)` work bound.  Temporary-array allocation remains outside
the advertised boundary.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
