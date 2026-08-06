# Chapter 30 Milestone 2 Design

## Goal

Close the remaining main-text boundary of CLRS third-edition Section 30.3,
*Efficient FFT implementations*, on top of the proved generic radix-2 core from
Milestone 1.

The milestone must provide:

- an executable bit-reversal copy on power-of-two vectors;
- an explicit bit-reversal index equivalence, with structural and numeric bit
  semantics and an involution theorem;
- an executable iterative radix-2 FFT built from flat butterfly stages;
- a stage-factorization invariant connecting those stages to the recursive FFT;
- proofs that the iterative FFT equals the recursive FFT and the generic DFT;
- execution-attached exact counts for bit-reversal moves, additions and
  subtractions, multiplications, arithmetic work, and total charged work;
- an explicit layered FFT network whose evaluation is the iterative FFT;
- exact butterfly count and butterfly-layer depth, together with primitive
  arithmetic-gate size and depth; and
- complete Chapter 30 repository, documentation, audit, and source navigation
  configuration closure.

At closure, Sections 30.1, 30.2, and 30.3 are `proved`.  Chapter 30 has no
remaining main-text gap within the strong boundary established below.
Chapter-end exercises and Problems 30-1 through 30-6 remain outside the
reviewed theorem-group denominator.

## Scope

### Included

- CLRS third-edition Section 30.3.
- Pure fixed-length power-of-two vectors.
- Exact arithmetic over the generic ring/field and primitive-root interfaces
  already established in Section 30.2.
- A functional bit-reversal copy and flat, explicitly indexed butterfly
  stages.
- Separate execution and arithmetic-circuit cost models.
- Power-of-two exact costs and the appropriate asymptotic consequences.
- Reader-facing section guides, interface tests, closure tests, proof audit,
  progress data, and source navigation metadata integration.

### Excluded

- Floating-point approximation and roundoff-error analysis.
- Mutable arrays, aliasing, in-place update semantics, and imperative loop
  verification.
- RAM, cache, allocator, SIMD, GPU, and communication-cost models.
- Parallel scheduling overhead, processor bounds, and a concrete runtime
  implementation.
- Number-theoretic-transform specialization and external code generation.
- Chapter-end exercises and Problems 30-1 through 30-6.

These exclusions must remain explicit in the section guide and proof map.  In
particular, the functional execution proves the mathematical content of the
CLRS iterative organization; it does not claim verification of a mutable-array
program.

## Approved Architecture

The implementation uses a hybrid flat-stage algorithm with a recursive proof
bridge.

```text
PowTwoVec K k
    |
    v
bitReverseExec
    |
    v
stage 0 -> stage 1 -> ... -> stage (k - 1)
    |
    v
iterativeRadix2FFTExec
    |
    +-- value
    +-- bitReversalMoves
    +-- addSubtractions
    +-- multiplications
```

The public algorithm is genuinely iterative at the stage level: it begins with
a flat bit-reversed vector and folds a sequence of flat stages over that
vector.  Correctness is not proved by expanding all raw index arithmetic at
once.  Instead, structural lemmas show that the first `k - 1` stages act
independently on the two contiguous halves and that the final stage is the
already proved Section 30.2 butterfly layer.  This yields the recursive FFT
equation and lets the existing recursive correctness theorem close the DFT
proof.

This route was selected over two alternatives:

1. a raw `Nat.testBit`, division, and modulo implementation for every stage,
   which is close to pseudocode but creates a large and fragile index-arithmetic
   proof surface; and
2. a matrix-first factorization, which is algebraically elegant but risks
   hiding the advertised executable loop and its actual counters.

Low-level bit semantics remain visible through a characterization theorem for
the bit-reversal equivalence.  Linear-operator or matrix corollaries are not a
closure requirement.

## Reuse Of The Milestone 1 Core

Section 30.3 imports Section 30.2 and reuses, rather than duplicates:

- `PowTwoVec`;
- `evenIndex`, `oddIndex`, `evenCoeffs`, and `oddCoeffs`;
- `lowerHalfIndex`, `upperHalfIndex`, and `joinHalves`;
- `TwiddleExecution` and successive twiddle generation;
- `ButterflyExecution`, `butterflyLayerExec`, and its exact counters;
- `FFTExecution`, `recursiveFFTExec`, and `recursiveFFT`;
- recursive FFT correctness against the generic DFT; and
- `radix2FFTWork` and its asymptotic infrastructure.

All new declarations live in `CLRS.Chapter30`.  Section 30.2 never imports
Section 30.3.

## Module Layout

```text
CLRSLean/Chapter_30.lean

CLRSLean/Chapter_30/
  Section_30_3_Efficient_FFT_Implementations.lean
  Section_30_3_Efficient_FFT_Implementations/
    BitReversal.lean
    IterativeFFT/
      Definitions.lean
      Correctness.lean
      Costs.lean
    ParallelFFT.lean
```

The section file is an aggregator and reader guide.  Definitions, correctness,
and costs remain in focused modules.  A module that grows beyond a reasonable
review surface is split only at a genuine theorem dependency.

## Bit-Reversal Model

### Index equivalence

`bitReverseEquiv k` is an equivalence

```text
Fin (2 ^ k) equiv Fin (2 ^ k)
```

defined recursively.  At a successor exponent, the input index is decomposed
into its least-significant bit and its remaining quotient; the quotient is
recursively reversed, and the former least-significant bit selects the output
half.  Product/finite-index equivalences and proved power-of-two equalities own
the casts.

The structural public laws state that reversing an even input index lands in
the lower half and reversing an odd input index lands in the upper half, with
the remaining index recursively reversed.  These laws are the primary rewrite
interface for later proofs.

The numeric characterization states, for every bit position below `k`, that
the corresponding bit of the result is the mirrored bit of the input.  It may
be expressed with `Nat.testBit` or through a proved fixed-width bit-vector
encoding if that produces the smaller stable proof surface.  In either form,
the theorem must connect back to the natural-number value of the public `Fin`
equivalence.

The equivalence is proved involutive.  Consequences include injectivity,
surjectivity, and the fact that applying the corresponding vector permutation
twice returns the original vector.

### Executable copy

`BitReverseExecution K k` contains:

- `value : PowTwoVec K k`; and
- `moves : Nat`.

`bitReverseExec` follows the recursive even/odd decomposition:

```text
bitReverseExec 0 a = one-element copy of a
bitReverseExec (k + 1) a =
  join the copied bit reversals of evenCoeffs a and oddCoeffs a
```

The value projection is `bitReverseCopy`.  Its main semantic theorem says that
the output at index `i` is the input at the inverse bit-reversed index; because
the equivalence is involutive, either direction reduces to the same public
index map.

Every source element contributes one output move.  Thus the execution proves
exactly `2 ^ k` moves, including one move in the singleton base case.  This is a
functional data-movement count, not a RAM write-cost theorem.

## Flat Butterfly Stages

An admissible stage is indexed by `s : Fin k`; invalid stage numbers are not
represented.  For a transform of exponent `k`, stage `s` has:

- block size `2 ^ (s + 1)`;
- half-block size `2 ^ s`;
- `2 ^ (k - s - 1)` blocks; and
- stage root `omega ^ (2 ^ (k - s - 1))`.

Finite-index equivalences decompose each flat vector position into a block,
half, and within-half offset.  No `Option` lookup or silent default value is
allowed.

For each block, the implementation extracts two contiguous half-vectors and
runs the existing `butterflyLayerExec` at the stage root.  A stage execution
stores or constructs these actual block runs, reassembles their values into a
flat vector, and sums their counter fields.  The exact stage-count theorem is
therefore a theorem about the value-producing execution, not an unrelated
closed formula.

The stage interface includes application equations for lower and upper
butterfly outputs.  These are the stable surface used by correctness and
network-evaluation proofs.

## Iterative Execution

`IterativeFFTExecution K k` contains:

- `value : PowTwoVec K k`;
- `bitReversalMoves : Nat`;
- `addSubtractions : Nat`; and
- `multiplications : Nat`.

The execution first runs `bitReverseExec`, then folds all `k` admissible stages
in increasing order, carrying the current vector and accumulated counters.
The public value projection is `iterativeRadix2FFT`.

The exponent-zero transform is the identity after its singleton bit-reversal
copy, has no stages, and has zero arithmetic work.  All definitions and closed
forms must handle this case without a positivity side condition.

## Correctness And Stage Invariant

The correctness proof exposes the following structural theorem family:

1. bit-reversal of a successor-size input is the join of the bit reversals of
   its even and odd coefficient vectors;
2. every nonfinal full-size stage preserves the two contiguous halves;
3. the first `k` stages of a size-`2 ^ (k + 1)` run factor into the complete
   size-`2 ^ k` stage runs of those halves under root `omega ^ 2`;
4. the final full-size stage is `butterflyLayer omega`; and
5. consequently, the iterative transform satisfies the same successor
   recurrence as `recursiveFFT`.

The factorization theorem is the principal stage invariant.  It describes how
the evolving flat state corresponds to the recursive subproblems, rather than
merely asserting equality after the final stage.

Structural induction then proves:

```text
iterativeRadix2FFT omega a = recursiveFFT omega a
```

for every ring and every input.  Under the existing characteristic-zero field
and primitive-root hypotheses, transitivity with Milestone 1 yields:

```text
iterativeRadix2FFT omega a = dft omega a
```

The DFT theorem must use the generic Section 30.2 interface.  A separate complex
principal-root wrapper is optional only if it can be a thin corollary; it must
not duplicate the generic proof.

## Execution-Attached Costs

The cost model separates data movement from arithmetic.

For length `N = 2 ^ k`:

- bit-reversal moves are exactly `N`;
- each stage performs exactly `N` additions/subtractions;
- each stage performs exactly `N` charged multiplications;
- all stages perform exactly `k * N` additions/subtractions;
- all stages perform exactly `k * N` multiplications;
- arithmetic work is exactly `2 * k * N`, equal to `radix2FFTWork k`; and
- total charged work is exactly `N + 2 * k * N`.

The multiplication count intentionally includes both the `N / 2` data-twiddle
products and the `N / 2` accumulator updates performed by the existing
successive twiddle generator in each stage.  Generating one shared twiddle
vector and then claiming the old per-block count is forbidden.

The milestone proves the corresponding `Theta(k * 2 ^ k)` arithmetic and total
work results.  It also defines padded iterative work using the existing
`fftExponent`, `fftCapacity`, and zero-padding execution bridge, proves the
exact power-of-two formula, and proves an all-input `Theta(n log n)` theorem by
the established adjacent-power argument.  No theorem may describe a
power-of-two-only formula as an all-input result.

## Parallel FFT Network

Section 30.3 defines a focused, typed layered network rather than forcing the
FFT wiring into a generic graph before its structure is proved.

The network contains exactly the admissible stages in increasing order.  Each
stage contains one butterfly for every block/within-half pair, together with
its fixed twiddle constant.  Network evaluation uses the same stage semantics
as the iterative execution, and the main evaluation theorem states that the
network computes `iterativeRadix2FFT` after bit-reversal wiring.

Logical circuit accounting assumes powers of `omega` are fixed circuit
constants.  Bit reversal is wiring and contributes no arithmetic gate.
Therefore:

- each stage has `2 ^ (k - 1)` butterflies for positive `k`;
- total butterfly count is `k * 2 ^ (k - 1)` using natural-number conventions
  that also reduce correctly at `k = 0`;
- butterfly-layer depth is exactly `k`;
- each butterfly expands to one multiplication and two addition/subtraction
  gates;
- primitive arithmetic-gate size is `3 * k * 2 ^ (k - 1)`; and
- primitive arithmetic-gate depth is at most, and for this explicit expansion
  exactly, `2 * k`.

This circuit count is deliberately distinct from execution work.  The
execution charges successive twiddle generation; the arithmetic circuit has
prewired twiddle constants.  Both models and their relationship must be stated
in theorem documentation.

The terminology aligns with Chapter 27's work/span distinction, but the main
theorems concern logical circuit size and depth.  A bridge to Chapter 27's
`CompDAG` or `SpawnTree` is included only if it preserves these semantics
without introducing scheduler/spawn overhead into the claimed circuit depth.

## Tests

The milestone adds focused compile-time interfaces, normally:

```text
Tests/Chapter_30_BitReversal_Interface.lean
Tests/Chapter_30_IterativeFFT_Interface.lean
Tests/Chapter_30_ParallelFFT_Interface.lean
Tests/Chapter_30_Milestone2_Closure.lean
```

Tests must exercise public definitions and headline theorems without unfolding
private implementation details.  RED tests are written before their production
interfaces.  The closure test prints axioms for the new final correctness,
exact-cost, and circuit-depth theorems.

The existing five Chapter 30 tests remain part of every final verification run.

## Documentation And Progress Closure

On completion:

- `CLRSLean/Chapter_30.lean` imports and links Section 30.3;
- the Section 30.3 guide identifies the proved and excluded boundaries;
- `docs/proof-map.csv` replaces the deferred Section 30.3 gap with reviewed
  theorem groups based on the actual final inventory;
- `CLRSLean/Status.lean`, `CLRSLean/Progress.lean`, and `README.md` use the same
  counts and status;
- site/repository consistency checks pass; and
- a Milestone 2 proof audit records declarations, exact commands, axiom
  surfaces, and remaining explicit exclusions.

The reviewed theorem-group count is derived from the final declarations and is
not predetermined in this design.

## Verification And Closure Criteria

The milestone is complete only when fresh output establishes all of the
following:

1. all nine expected Chapter 30 interface and closure tests compile;
2. the new final theorems use only accepted foundational axioms such as
   `propext`, `Classical.choice`, and `Quot.sound`, with no project axiom;
3. repository checks, proof-map checks, progress checks, README checks, and
   site-status checks pass;
4. no `sorry`, `admit`, placeholder implementation, or undeclared theorem
   assumption occurs in the new boundary;
5. `lake build CLRSLean` succeeds;
6. the worktree is clean after the final audit commit.

Website generation, preparation, rendering inspection, and deployment are a
separate publishing task.  They are not Chapter 30 proof-closure gates unless
the user explicitly requests that publishing work.

Implementation follows small RED/GREEN/refactor commits.  Any unexpected Lean
failure triggers the repository's systematic-debugging workflow before a fix
is proposed.  Completion claims follow fresh verification output rather than
earlier runs.
