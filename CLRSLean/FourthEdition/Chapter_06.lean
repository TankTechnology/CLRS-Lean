import CLRSLean.FourthEdition.Chapter_06.Section_06_1_Heaps
import CLRSLean.FourthEdition.Chapter_06.Section_06_2_Maintaining_Heap_Property
import CLRSLean.FourthEdition.Chapter_06.Section_06_3_Building_A_Heap
import CLRSLean.FourthEdition.Chapter_06.Section_06_4_Heapsort
import CLRSLean.FourthEdition.Chapter_06.Section_06_4_Heapsort.CostedExecution
import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues
import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues.Insert

/-!
# Chapter 6 — Heapsort

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 6.1--6.5 are native fourth-edition sections (heaps, maintaining the
heap property, building a heap, the heapsort algorithm, and priority queues),
imported directly from
[Section 6.1](CLRSLean/FourthEdition/Chapter_06/Section_06_1_Heaps/),
[Section 6.2](CLRSLean/FourthEdition/Chapter_06/Section_06_2_Maintaining_Heap_Property/),
[Section 6.3](CLRSLean/FourthEdition/Chapter_06/Section_06_3_Building_A_Heap/),
[Section 6.4](CLRSLean/FourthEdition/Chapter_06/Section_06_4_Heapsort/), and
[Section 6.5](CLRSLean/FourthEdition/Chapter_06/Section_06_5_Priority_Queues/).
Section 6.4 includes the nested costed-execution development.  Declarations
retain the `CLRS.Chapter06` namespace during the compatibility period; the
third-edition-numbered imports {lit}`CLRSLean.Chapter_06` and
{lit}`CLRSLean.Chapter_06.Section_06_*` forward to these sources.

## Implementation details

The supporting implementation page remains available outside the main sidebar:

* [Costed Heapsort Execution](CLRSLean/FourthEdition/Chapter_06/Section_06_4_Heapsort/CostedExecution/)
* [Array-level MAX-HEAP-INSERT](CLRSLean/FourthEdition/Chapter_06/Section_06_5_Priority_Queues/Insert/)

## Coverage boundary

The represented heap and priority-queue correctness developments are reused.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
