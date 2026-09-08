import CLRSLean.Chapter_32
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher
import CLRSLean.FourthEdition.Chapter_32.Section_32_2_Rabin_Karp
import CLRSLean.FourthEdition.Chapter_32.Section_32_3_Finite_Automata
import CLRSLean.FourthEdition.Chapter_32.Section_32_4_Knuth_Morris_Pratt
import CLRSLean.FourthEdition.Chapter_32.Section_32_5_Suffix_Arrays
import CLRSLean.FourthEdition.Chapter_32.Section_32_2_Rabin_Karp.CachedPower
import CLRSLean.FourthEdition.Chapter_32.Section_32_3_Finite_Automata.CachedScan

/-!
# Chapter 32 — String Matching

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Section 32.1 is a native fourth-edition section (the string model with the
naive matcher), imported directly from
[Section 32.1](CLRSLean/FourthEdition/Chapter_32/Section_32_1_String_Model/).
Section 32.2 (the Rabin-Karp algorithm) is a native fourth-edition section in
[Section 32.2](CLRSLean/FourthEdition/Chapter_32/Section_32_2_Rabin_Karp/).
Section 32.3 (string matching with finite automata) is a native fourth-edition
section in
[Section 32.3](CLRSLean/FourthEdition/Chapter_32/Section_32_3_Finite_Automata/).
Section 32.4 (the Knuth-Morris-Pratt algorithm) is a native fourth-edition
section in
[Section 32.4](CLRSLean/FourthEdition/Chapter_32/Section_32_4_Knuth_Morris_Pratt/).
Section 32.5 (suffix arrays) is a native fourth-edition section in
[Section 32.5](CLRSLean/FourthEdition/Chapter_32/Section_32_5_Suffix_Arrays/).
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_32` and
{lit}`CLRSLean.Chapter_32.Section_32_*` forward to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Naive Matcher Implementation](CLRSLean/FourthEdition/Chapter_32/Section_32_1_String_Model/Naive_Matcher/)

## Coverage boundary

The native sections supply the represented fourth-edition string-matching
sections (§32.1, §32.2, §32.3, §32.4, and §32.5).
{lit}`RKExecution.execute` prepares the high-position power and both seed
hashes once, then uses seven fixed scalar arithmetic operations per slide.
The returned shifts refine the naive matcher, including empty and oversized
patterns. Power/seed counters are actual recursions; confirmation remains the
stated per-hit budget, excluding list movement, symbol-map and bit costs.

{lit}`DFAExecution.execute` builds one table and passes it explicitly into a
scan that counts one transition request per character. The table-cell count
excludes suffix search inside {lit}`delta`; list and alphabet lookup are not
constant-time. No efficient table-construction runtime is claimed.

Suffix-array sorting counts whole-suffix comparisons, not character work.
Binary queries exclude construction, list indexing and result materialization.
Their empty-pattern results range over stored positions {lit}`0,...,n-1`,
omitting the terminal boundary {lit}`n`. KMP retains its proved execution
control-step metric and its existing storage-cost boundary.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
