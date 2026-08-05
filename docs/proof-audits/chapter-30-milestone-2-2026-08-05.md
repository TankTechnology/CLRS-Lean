# Chapter 30 Milestone 2 Audit — 2026-08-05

## Scope

This audit closes CLRS third-edition Section 30.3 on top of the Milestone 1
Sections 30.1--30.2 core.  The completed exact functional boundary contains:

- a total bit-reversal equivalence, numeric bit semantics, involution, and an
  executable copy with exactly `2^k` moves;
- globally ordered iterative radix-2 stages and the stage-prefix
  half-factorization invariant;
- equality of the iterative transform with the recursive FFT and generic DFT;
- execution-attached exact arithmetic, total, and padded all-input work;
- a layered FFT network whose recursive stage syntax stores one actual gate at
  every butterfly offset;
- gate-family and stage-circuit evaluation bridges to the verified iterative
  transform; and
- exact butterfly, primitive-gate, and depth counts derived from that same
  stored syntax.

Mutable/in-place arrays and aliasing, RAM/cache/allocator/hardware costs,
floating-point approximation and numerical stability, concrete scheduling and
processor bounds, number-theoretic-transform specialization, code generation,
exercises, and Problems 30-1 through 30-6 remain outside the reviewed boundary.
They do not reopen the completed main-text theorem groups.

## Source and theorem inventory

The Section 30.3 surface consists of the reader guide plus six implementation
modules:

- `Section_30_3_Efficient_FFT_Implementations.lean`;
- `BitReversal.lean`;
- `IterativeFFT.lean`;
- `IterativeFFT/Definitions.lean`;
- `IterativeFFT/Correctness.lean`;
- `IterativeFFT/Costs.lean`; and
- `ParallelFFT.lean`.

The Milestone 2 closure interface reviews 17 new headline groups: five
bit-reversal groups; the stage-prefix invariant and iterative successor
equation; equality with recursive FFT and DFT; exact arithmetic work, exact
total work, and padded all-input `Theta(n log n)` work; network evaluation; and
the four butterfly/gate size-and-depth results.  Together with Milestone 1,
Chapter 30 records 46 tracked and 46 proved groups with zero missing core
groups.

The two cost conventions are intentionally separate:

- functional execution arithmetic: `2 * k * 2^k`;
- functional execution total: `2^k + 2 * k * 2^k`;
- circuit butterflies: `k * 2^(k-1)`;
- circuit primitive gates: `3 * k * 2^(k-1)`;
- butterfly-layer depth: `k`; and
- primitive arithmetic-gate depth: `2 * k`.

Execution charges successive twiddle generation and bit-reversal moves.  The
circuit treats twiddle powers as constants and bit reversal as wiring.  Its
`FFTButterflyGate`, `ButterflyLayerCircuit`, and `FFTStageCircuit` hierarchy is
not merely descriptive metadata: `FFTNetwork.eval`, butterfly count, and depth
all recurse through the circuits stored by the layers.  The bridge theorems
`canonicalButterflyLayerCircuit_eval` and `fftStageCircuit_eval` connect this
representation to the previously verified functional stage semantics.

## Kernel and axiom evidence

`Tests/Chapter_30_Milestone2_Closure.lean` printed these exact dependency
surfaces:

- `bitReverseEquiv_testBit`, `bitReverseCopy_involutive`,
  `iterativeRadix2FFT_eq_recursiveFFT`, `iterativeRadix2FFT_eq_dft`,
  `paddedIterativeFFTWork_allInput_bigTheta`,
  `canonicalButterflyLayerCircuit_eval`, `fftStageCircuit_eval`,
  `fftNetwork_eval`, `fftNetwork_butterflyCount`, and
  `fftNetwork_primitiveDepth`: `propext`, `Classical.choice`, `Quot.sound`;
  and
- `iterativeRadix2FFTExec_totalWork`: `propext`, `Quot.sound`.

No `sorryAx` or project-defined axiom appears.  A direct scan of the Section
30.3 guide and implementation directory found no `sorry`, `admit`, `sorryAx`,
or axiom declaration.

## Verification evidence

The following fresh commands ran on 2026-08-05 and exited 0:

| Command | Observed evidence |
|---|---|
| `lake build +CLRSLean.Chapter_30` | 10.25 s; build completed successfully, 8,603 jobs |
| `lake env lean Tests/Chapter_30_Interface.lean` | 3.60 s |
| `lake env lean Tests/Chapter_30_DFT_Interface.lean` | 3.72 s |
| `lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean` | 3.54 s; printed accepted Milestone 1 axiom surfaces |
| `lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean` | 3.62 s |
| `lake env lean Tests/Chapter_30_Milestone1_Closure.lean` | 3.44 s; no `sorryAx` or project axiom |
| `lake env lean Tests/Chapter_30_BitReversal_Interface.lean` | 3.51 s |
| `lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean` | 3.36 s |
| `lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean` | 3.45 s; a noncanonical stored-gate regression passed; two non-blocking `unnecessarySimpa` linter warnings |
| `lake env lean Tests/Chapter_30_Milestone2_Closure.lean` | 3.30 s; axiom output recorded above |
| unfinished-proof scan over Section 30.3 | no matches; expected `rg` status 1 normalized to success |
| `uv run python scripts/check_progress_csv.py` | 0.02 s; 35 chapters, 1,793 tracked, 1,793 proved |
| `uv run python scripts/gen_readme_table.py --check` | 0.02 s; current |
| `uv run python scripts/check_repository.py` | 1.12 s; all repository checks passed |
| `uv run python scripts/check_site_consistency.py` | 0.04 s; 33 chapter guides, 293 section files, 338 literate modules |
| `git diff --check` | clean |
| `lake build CLRSLean` | 4.49 s; build completed successfully, 8,921 jobs |

Website generation, rendering inspection, preparation, and deployment are a
separate publishing task under the project workflow.  They are not proof
closure gates and are not used as evidence in this audit.

## Pre-merge review

The final review compared the clean Chapter 30 branch with current
`origin/main`, inspected the representation, DFT, recursive and iterative FFT,
polynomial-multiplication, circuit, test, progress, and navigation surfaces,
and found no remaining critical or important semantic issue.  The review did
repair three documentation-quality gaps before merge:

- the Section 30.2 guide no longer describes completed Section 30.3 as
  deferred;
- README, reviewer, and build-agent instructions now consistently reserve
  website generation and rendered-navigation inspection for explicitly
  requested publishing work; and
- every declaration in the new Chapter 30 source tree now has the declaration
  documentation required by `CLAUDE.md`.

Fresh post-repair verification observed:

- `lake build +CLRSLean.Chapter_30`: success, 8,603 jobs;
- all nine `Tests/Chapter_30_*.lean` files: success;
- closure axiom output: only `propext`, `Classical.choice`, and `Quot.sound`;
- unfinished-proof, unsafe/opaque declaration, production `native_decide`, and
  missing declaration-documentation scans: no matches;
- progress, README, repository, local-link, placeholder, and source-navigation
  checks: success, with 1,793 tracked and 1,793 proved entries; and
- `lake build CLRSLean`: success, 8,921 jobs in 4.68 seconds.

No Verso HTML build, rendered-site inspection, or deployment was performed.
