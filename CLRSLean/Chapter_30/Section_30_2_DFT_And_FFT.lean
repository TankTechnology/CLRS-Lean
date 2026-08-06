import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S1_RootsOfUnity
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S2_DFT
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S3_InversionAndConvolution
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Definitions
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Correctness
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Costs
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.PolynomialMultiplication

/-! # Section 30.2 - The DFT and FFT

The generic algebraic core works over characteristic-zero fields: primitive
roots supply orthogonality, the positive-exponent CLRS transform is polynomial
evaluation at powers of a root, and `idft` gives both inverse directions.
Fourier-space pointwise multiplication is connected to cyclic convolution and,
under an explicit capacity premise, to ordinary polynomial multiplication.
The actual radix-2 FFT recursively splits even and odd coefficients, reuses a
successively generated twiddle trace, combines the children through a butterfly
layer, and supplies an inverse agreeing with `idft`.  Its arithmetic counters
are projections of the same execution: each counter is exactly `k * 2^k`, and
zero padding lifts the total work to an all-input `Theta(n log n)` theorem.

`complexDft_mathlib` is the separate compatibility boundary with Mathlib's
complex `ZMod.dft`; its statement exposes the required output-index sign change.
The generic FFT multiplication execution is correct under the minimal no-wrap
capacity premise; the complex wrapper constructs a sufficient power-of-two
capacity and primitive root internally.  The multiplication work field charges
three recursive transforms, pointwise products, and inverse scaling, with an
exact composition and an all-input `Theta(n log n)` bound.  Section 30.3 builds
the iterative and layered-circuit refinements on this recursive core.

Implementation pages:

- [Roots of unity](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity/)
- [Generic DFT and complex compatibility](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT/)
- [Inversion and convolution](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution/)
- [Recursive radix-2 FFT](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/)
- [Recursive FFT definitions](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions/)
- [Recursive FFT correctness](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Correctness/)
- [Recursive FFT costs](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs/)
- [FFT polynomial multiplication](CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication/)
-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
