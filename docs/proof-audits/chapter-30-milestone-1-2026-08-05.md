# Chapter 30 Milestone 1 Audit — 2026-08-05

## Scope

This audit covers the approved strong boundary for CLRS Sections 30.1–30.2:
fixed coefficient and point-value representations, generic DFT algebra over
characteristic-zero fields, an actual radix-2 recursive FFT and inverse,
generic FFT polynomial multiplication, and an unconditional exact complex
wrapper.  Transform vectors have power-of-two size and twiddles are generated
successively by the same execution whose counters are analyzed.

The exact FFT work theorem is `2 * k * 2^k`.  The exact multiplication
composition is `3 * radix2FFTWork k + 2 * 2^k`, including both pointwise
products and inverse scaling.  `paddedFFTWork_allInput_bigTheta` and
`fftMultiplyWork_allInput_bigTheta` give the two advertised all-input
`Theta(n log n)` bounds.

Section 30.3 (bit reversal, iterative FFT/stage invariants, and parallel FFT
circuit depth/size), mutable arrays and RAM semantics, floating-point error and
numerical stability, and end-of-chapter exercises/problems are excluded.

## Kernel and interface evidence

The five Chapter 30 interface tests expose the representation, DFT/inverse,
recursive FFT, multiplication, execution-erasure, exact-cost, and all-input
asymptotic theorem families.  The closure test prints axioms for the headline
theorems.  Observed dependencies are only Lean/Mathlib standard principles:
`propext`, `Classical.choice`, and `Quot.sound`; the direct execution erasure
also omits `Classical.choice`.  No `sorryAx` or project-defined axiom appears.

## Verification evidence

The following commands have been run on 2026-08-05 and exited 0:

- `lake build +CLRSLean.Chapter_30`
- `lake env lean Tests/Chapter_30_Interface.lean`
- `lake env lean Tests/Chapter_30_DFT_Interface.lean`
- `lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean`
- `lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean`
- `lake env lean Tests/Chapter_30_Milestone1_Closure.lean`
- `uv run python scripts/check_repository.py`
- `uv run python scripts/check_site_consistency.py`
- `uv run python scripts/check_progress_csv.py`
- `uv run python scripts/gen_readme_table.py --check`
- `lake build CLRSLean` (8,778 jobs)
- `lake build :literateHtml` (9,189 jobs)
- `git diff --check`

The repository check reports 1,705 tracked theorem entries and 1,705 proved,
30 chapter guide pages, 29 chapters with section files, 153 section files,
and 195 literate modules.  The direct unfinished-proof scan
`rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_30 -g '*.lean'` produced no
matches (the expected `rg` exit status 1).
