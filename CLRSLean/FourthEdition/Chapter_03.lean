import CLRSLean.FourthEdition.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions

/-!
# Chapter 3 — Characterizing Running Times

Native fourth-edition chapter guide.

## Current source

This guide sources fourth-edition §§3.1--3.2 from
{lit}`CLRSLean.FourthEdition.Chapter_03.Section_03_1_Asymptotic_Notation` and §3.3
from {lit}`CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions`.
Declarations retain the {lit}`CLRS.Chapter03` namespace; the legacy import
{lit}`CLRSLean.Chapter_03` forwards to this guide during the compatibility
period.

## Coverage boundary

The asymptotic-notation facade supplies fourth-edition §§3.1--3.2.  Its core
defines the five asymptotic relations, while its textbook bridge proves their
equivalence to the eventually nonnegative CLRS formulations, strict
{lit}`o`/{lit}`ω` characterizations, transitivity, and real-domain variants.

The standard-functions facade supplies §3.3 through small theorem modules.  It
includes the textbook floor, ceiling, remainder, exponential, logarithmic,
iteration, Fibonacci, and factorial identities; real-exponent growth bridges;
arbitrary nonzero-polynomial leading-term asymptotics; the extended growth
hierarchy through {lit}`n^(log n)` and {lit}`n^n`; and the exact effective
Robbins refinement of Stirling's formula.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
