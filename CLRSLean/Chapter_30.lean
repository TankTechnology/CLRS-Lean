import CLRSLean.Chapter_30.Section_30_1_DFT_FFT
import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT

/-!
# Chapter 30 — Polynomials and the FFT

Chapter 30 of CLRS covers polynomial multiplication via the Discrete Fourier
Transform (DFT) and the Fast Fourier Transform (FFT).

This formalization currently covers:

* **30.1–30.2 DFT and FFT** — complex roots of unity `ω(n)`, the DFT and
  inverse DFT definitions, and the divide-and-conquer recursive formulation.

* **30.3 Efficient FFT implementations** — bit-reversal permutation, the
  iterative in-place Cooley-Tukey butterfly network, and the equivalence
  with the DFT.

## Sections

* **30.1–30.2 DFT and FFT.**
  Main definitions:
  `CLRS.Chapter30.ω`,
  `CLRS.Chapter30.evalPoly`,
  `CLRS.Chapter30.pointValues`,
  `CLRS.Chapter30.dft`,
  `CLRS.Chapter30.idft`.

* **30.3 Efficient FFT.**
  Main definitions:
  `CLRS.Chapter30.bitReverse`,
  `CLRS.Chapter30.bitReverseCopy`,
  `CLRS.Chapter30.iterativeFFT`,
  `CLRS.Chapter30.fft`.
  Main theorems:
  `CLRS.Chapter30.iterativeFFT_eq_dft`,
  `CLRS.Chapter30.bitReverse_bitReverse`.

## Future work

* 30.2 The recursive FFT algorithm (divide-and-conquer formulation).
* Full correctness proofs for the iterative FFT.
* Polynomial multiplication via FFT.

-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
