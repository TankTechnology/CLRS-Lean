import CLRSLean.Chapter_21
import CLRSLean.FourthEdition.Chapter_19.Section_19_1_Disjoint_Set_Operations
import CLRSLean.FourthEdition.Chapter_19.Section_19_2_Linked_List_Representation
import CLRSLean.FourthEdition.Chapter_19.Section_19_3_Disjoint_Set_Forests
import CLRSLean.FourthEdition.Chapter_19.Section_19_4_Analysis
import CLRSLean.FourthEdition.Chapter_19.Section_19_4_Analysis.CostedExecution
import CLRSLean.FourthEdition.Chapter_19.Section_19_4_Analysis.InverseAckermann

/-!
# Chapter 19 — Data Structures for Disjoint Sets

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 19.1--19.4 are native fourth-edition sections (disjoint-set
operations, the linked-list representation, disjoint-set forests, and the
union-by-rank/path-compression analysis), imported directly from
[Section 19.1](CLRSLean/FourthEdition/Chapter_19/Section_19_1_Disjoint_Set_Operations/),
[Section 19.2](CLRSLean/FourthEdition/Chapter_19/Section_19_2_Linked_List_Representation/),
[Section 19.3](CLRSLean/FourthEdition/Chapter_19/Section_19_3_Disjoint_Set_Forests/),
and
[Section 19.4](CLRSLean/FourthEdition/Chapter_19/Section_19_4_Analysis/).
Section 19.4 includes the nested costed-execution and inverse-Ackermann
amortization developments.  Declarations retain the legacy `CLRS.Chapter21`
namespace during the compatibility period; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_21` and {lit}`CLRSLean.Chapter_21.Section_21_*`
forward to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Costed Union-Find Execution](CLRSLean/FourthEdition/Chapter_19/Section_19_4_Analysis/CostedExecution/)
* [Inverse-Ackermann Amortization](CLRSLean/FourthEdition/Chapter_19/Section_19_4_Analysis/InverseAckermann/)

## Coverage boundary

The native sections supply all represented fourth-edition disjoint-set
sections.  The namespace migration `CLRS.Chapter21` → `CLRS.Chapter19` is
tracked chapter by chapter.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
