import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model
import CLRSLean.FourthEdition.Chapter_32.Section_32_1_String_Model.Naive_Matcher
import CLRSLean.FourthEdition.Chapter_32.Section_32_2_Rabin_Karp

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
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_32` and
{lit}`CLRSLean.Chapter_32.Section_32_*` forward to these sources.

## Coverage boundary

The native sections supply the represented fourth-edition string-matching
sections (§32.1 and §32.2).  The remaining fourth-edition sections (§32.3--32.5:
string matching with finite automata, the Knuth-Morris-Pratt algorithm, and
suffix arrays) are not started.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
