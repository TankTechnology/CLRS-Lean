import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials
import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S1_CoefficientVectors
import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S2_PointValueInterpolation
import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S3_RepresentationOperations
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S1_RootsOfUnity
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S2_DFT
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S3_InversionAndConvolution
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Definitions
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Correctness
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Costs
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.PolynomialMultiplication
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Definitions
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Correctness
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Costs
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.ParallelFFT

/-! # Chapter 30 - Polynomials and the FFT

Sections 30.1--30.3 are complete within the exact generic-arithmetic
functional boundary. The 46 tracked theorem groups are all kernel checked;
the chapter has no remaining main-text group inside this reviewed model.

## Proof architecture

The development follows the textbook dependency chain. Section 30.1 fixes
coefficient and point-value representations and proves their bridges and
operations. Section 30.2 builds generic DFT algebra on those representations,
proves inversion and convolution, implements the recursive radix-2 FFT, and
uses it for polynomial multiplication. Section 30.3 factors the same transform
into bit-reversal copying and globally ordered iterative stages, then stores
those stages as an evaluated layered circuit whose size and depth are read from
the same syntax.

## Section 30.1 - Representing polynomials

- {name}`CLRS.Chapter30.coeffVector_vectorToPolynomial` and
  {name}`CLRS.Chapter30.vectorToPolynomial_coeffVector` give the fixed-capacity
  coefficient round trips.
- {name}`CLRS.Chapter30.interpolate_pointValues_roundTrip` proves the
  distinct-node interpolation round trip.
- {name}`CLRS.Chapter30.hornerEval_correct` connects Horner evaluation to
  polynomial evaluation.
- {name}`CLRS.Chapter30.schoolbookMul_correct` and
  {name}`CLRS.Chapter30.schoolbookMulWork_exact` prove schoolbook
  multiplication and its exact represented work.

## Section 30.2 - The DFT and recursive FFT

- {name}`CLRS.Chapter30.idft_dft`, {name}`CLRS.Chapter30.dft_idft`, and
  {name}`CLRS.Chapter30.dft_cyclicConvolution` provide the Fourier algebra.
- {name}`CLRS.Chapter30.recursiveFFT_eq_dft` proves the executable recursive
  radix-2 transform computes the generic DFT.
- {name}`CLRS.Chapter30.complexFFTMultiply_correct` gives the unconditional
  automatically padded complex polynomial-multiplication wrapper.
- {name}`CLRS.Chapter30.paddedFFTWork_allInput_bigTheta` and
  {name}`CLRS.Chapter30.fftMultiplyWork_allInput_bigTheta` give the all-input
  {lit}`Theta(n log n)` work bounds.

## Section 30.3 - Iterative FFT and the layered network

- {name}`CLRS.Chapter30.bitReverseEquiv_testBit` and
  {name}`CLRS.Chapter30.bitReverseCopy_involutive` specify bit reversal.
- {name}`CLRS.Chapter30.iterativeRadix2FFT_eq_recursiveFFT` and
  {name}`CLRS.Chapter30.iterativeRadix2FFT_eq_dft` close the iterative
  algorithmic and algebraic bridges.
- {name}`CLRS.Chapter30.iterativeRadix2FFTExec_totalWork` and
  {name}`CLRS.Chapter30.paddedIterativeFFTWork_allInput_bigTheta` attach exact
  and asymptotic work to the executed iterative transform.
- {name}`CLRS.Chapter30.fftNetwork_eval`,
  {name}`CLRS.Chapter30.fftNetwork_butterflyCount`, and
  {name}`CLRS.Chapter30.fftNetwork_primitiveDepth` connect the stored circuit
  to transform semantics, exact size, and exact depth.

## Cost conventions

The functional and circuit models intentionally charge different objects:

- recursive or iterative arithmetic work is {lit}`2 * k * 2^k`;
- iterative total work, including bit-reversal moves, is
  {lit}`2^k + 2 * k * 2^k`;
- the layered circuit contains {lit}`k * 2^(k-1)` butterflies and
  {lit}`3 * k * 2^(k-1)` primitive arithmetic gates; and
- butterfly depth is {lit}`k`, while primitive arithmetic depth is
  {lit}`2 * k`.

Execution charges successive twiddle generation and data movement. Circuit
counting treats fixed twiddle powers as constants and bit reversal as wiring.

## Reviewed boundary

The represented algorithms are pure functions over fixed-length and
power-of-two vectors, over exact generic ring or characteristic-zero field
arithmetic as required by each theorem. Mutable arrays, aliasing, imperative
loops, RAM/cache/allocator and hardware costs, floating-point approximation and
numerical stability, concrete parallel scheduling, number-theoretic-transform
specialization, external code generation, exercises, and Problems 30-1 through
30-6 are optional extension tracks rather than missing core groups.
-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
