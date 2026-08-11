import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework
import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework.Section_16_2_Stack_And_Counter
import CLRSLean.FourthEdition.Chapter_16.Section_16_4_Dynamic_Tables
import CLRSLean.FourthEdition.Chapter_16.Section_16_4_Dynamic_Tables.Section_16_4_Mutable_Array_Tables

/-!
# Chapter 16 — Amortized Analysis

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 16.1--16.4 are native fourth-edition sections (the aggregate,
accounting, and potential-method framework; the stack and counter examples;
and the dynamic-tables development), imported directly from
[Section 16.1](CLRSLean/FourthEdition/Chapter_16/Section_16_1_Amortized_Framework/),
[Section 16.2](CLRSLean/FourthEdition/Chapter_16/Section_16_1_Amortized_Framework/Section_16_2_Stack_And_Counter/),
and
[Section 16.4](CLRSLean/FourthEdition/Chapter_16/Section_16_4_Dynamic_Tables/).
Declarations retain the legacy `CLRS.Chapter17` namespace during the
compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_17` and {lit}`CLRSLean.Chapter_17.Section_17_*` forward
to these sources.

## Coverage boundary

The native sections supply the fourth-edition amortized-analysis facade
(§16.1 aggregate analysis, §16.2 the accounting method, §16.3 the potential
method, §16.4 dynamic tables).  The namespace migration
`CLRS.Chapter17` → `CLRS.Chapter16` is tracked chapter by chapter.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
