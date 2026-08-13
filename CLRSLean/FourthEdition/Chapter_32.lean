import CLRSLean.Chapter_32
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher
import CLRSLean.FourthEdition.Chapter_32.Section_32_2_Rabin_Karp
import CLRSLean.FourthEdition.Chapter_32.Section_32_3_Finite_Automata
import CLRSLean.FourthEdition.Chapter_32.Section_32_4_Knuth_Morris_Pratt
import CLRSLean.FourthEdition.Chapter_32.Section_32_5_Suffix_Arrays

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

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
