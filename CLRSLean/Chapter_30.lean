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

Sections 30.1--30.3 are proved within the exact generic-arithmetic boundary.
The development covers fixed coefficient and point-value representations,
generic DFT algebra and inversion, recursive radix-2 FFT, generic and padded
complex polynomial multiplication, bit-reversal copying, iterative FFT stages
and their recursive factorization invariant, equality of the iterative FFT
with the recursive FFT and DFT, exact execution-derived work, all-input
`Theta(n log n)` bounds, and explicit FFT circuit size and depth.

The represented algorithms are pure functions over fixed-length vectors.
Mutable arrays, aliasing, imperative loops, RAM/cache/allocator and hardware
costs, floating-point approximation and numerical stability, concrete parallel
scheduling, number-theoretic-transform specialization, external code
generation, exercises, and Problems 30-1 through 30-6 remain outside the
reviewed theorem-group boundary.
-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
