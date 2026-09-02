import CLRSLean.FourthEdition.Chapter_10.Section_10_1_Simple_Array_Based_Data_Structures
import CLRSLean.FourthEdition.Chapter_10.Section_10_2_Linked_Lists
import CLRSLean.FourthEdition.Chapter_10.Section_10_3_Representing_Rooted_Trees

/-!
# Chapter 10 — Elementary Data Structures

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 10.1--10.3 are native fourth-edition sections (simple array-based data
structures, linked lists, and representing rooted trees), imported directly from
[Section 10.1](CLRSLean/FourthEdition/Chapter_10/Section_10_1_Simple_Array_Based_Data_Structures/),
[Section 10.2](CLRSLean/FourthEdition/Chapter_10/Section_10_2_Linked_Lists/), and
[Section 10.3](CLRSLean/FourthEdition/Chapter_10/Section_10_3_Representing_Rooted_Trees/).
Section 10.3 re-homes the legacy third-edition §10.4 rooted-tree source.
Declarations retain the `CLRS.Chapter10` namespace during the compatibility
period; the third-edition-numbered imports {lit}`CLRSLean.Chapter_10` and
{lit}`CLRSLean.Chapter_10.Section_10_*` forward to these sources.

## Coverage boundary

The legacy stack, queue, list, and rooted-tree developments are reused, together
with the fourth-edition §10.1 array-backed stack and queue interface
(top/head/tail pointers with overflow, underflow, and circular wrap-around).
Concrete RAM execution and pointer memory remain deferred.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
