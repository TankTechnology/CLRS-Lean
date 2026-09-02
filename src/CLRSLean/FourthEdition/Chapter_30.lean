import CLRSLean.Chapter_30
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

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Fixed-Capacity Coefficient Vectors](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors/)
* [Point-Value Interpolation](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S2_PointValueInterpolation/)
* [Representation Operations](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S3_RepresentationOperations/)
* [Roots of Unity](CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity/)
* [The Generic DFT](CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT/)
* [Inversion and Convolution](CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution/)
* [Recursive Radix-2 FFT](CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/)
* [FFT Polynomial Multiplication](CLRSLean/FourthEdition/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication/)
* [Bit-Reversal Permutation](CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal/)
* [Iterative Radix-2 FFT](CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/)
* [Parallel Network Size and Depth](CLRSLean/FourthEdition/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT/)

## Coverage boundary

The native sections supply the represented fourth-edition polynomial/FFT
sections (the FFT correctness and work analysis, the bit-reversal and
iterative-FFT implementations, and the parallel FFT).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
