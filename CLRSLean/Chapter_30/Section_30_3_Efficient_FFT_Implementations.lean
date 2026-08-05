import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.ParallelFFT

/-! # Section 30.3 - Efficient FFT implementations

The total bit-reversal permutation exposes structural even/odd laws,
fixed-width bit semantics, involution, and an exact one-move-per-element count.
The functional iterative FFT folds globally ordered stages over that
permutation.  Its stage-prefix invariant factors every nonfinal stage over the
two contiguous halves, proving equality with the recursive FFT and the generic
DFT.  The execution records exactly one bit-reversal move per input,
`k * 2^k` additions/subtractions, and `k * 2^k` multiplications; padding lifts
the total work to the all-input `Theta(n log n)` scale.

The explicit layered network stores recursive stage circuits whose leaves are
actual butterflies with fixed twiddle constants.  Evaluating those stored
gates is proved equal to the iterative FFT, and the same circuit syntax has
`k * 2^(k-1)` butterflies and butterfly depth `k`; expanding a butterfly to
one multiplication and two addition/subtraction gates gives
`3 * k * 2^(k-1)` primitive gates and primitive depth `2 * k`.  Twiddle powers
are circuit constants and bit reversal is wiring in this circuit model, while
the functional execution separately charges successive twiddle updates.

Mutable arrays, aliasing and in-place loop semantics; RAM, cache, allocator,
SIMD, GPU, and communication costs; parallel scheduling and processor bounds;
floating-point error and numerical stability; number-theoretic-transform
specialization; code generation; exercises; and Problems 30-1 through 30-6
remain outside this exact functional boundary.

Implementation pages:

- [Bit-reversal permutation](CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/BitReversal/)
- [Iterative FFT guide](CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/)
- [Iterative FFT definitions](CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Definitions/)
- [Iterative FFT correctness](CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Correctness/)
- [Iterative FFT costs](CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs/)
- [Parallel FFT network](CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT/)
-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
