import CLRSLean.FourthEdition.Chapter_30.Section_30_1_Representing_Polynomials
import CLRSLean.FourthEdition.Chapter_30.Section_30_2_DFT_And_FFT
import CLRSLean.FourthEdition.Chapter_30.Section_30_3_Efficient_FFT_Implementations

/-!
# Chapter 30 — Polynomials and the FFT

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 30.1--30.3 are native fourth-edition sections (representing
polynomials, the DFT and FFT, and efficient FFT implementations), imported
directly from
[Section 30.1](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/),
[Section 30.2](CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/),
and
[Section 30.3](CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/).
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_30` and
{lit}`CLRSLean.Chapter_30.Section_30_*` forward to these sources.

## Coverage boundary

The native sections supply the represented fourth-edition polynomial/FFT
sections (the FFT correctness and work analysis, the bit-reversal and
iterative-FFT implementations, and the parallel FFT).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
