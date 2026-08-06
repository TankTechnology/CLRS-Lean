# Chapter 30 Milestone 1 Design

## Goal

Complete the main-text theorem boundary of CLRS third-edition Sections 30.1
and 30.2, *Representing polynomials* and *The DFT and FFT*, while leaving
Section 30.3 as the chapter's single explicit main-text gap.

The milestone must provide:

- coefficient and point-value polynomial representations, with an exact bridge
  to Mathlib polynomials;
- interpolation existence and uniqueness at distinct sample points;
- the main operation semantics and arithmetic-cost contrast between coefficient
  and point-value representations;
- a generic discrete Fourier transform over a characteristic-zero field with a
  suitable primitive root of unity;
- Fourier inversion and the convolution theorem;
- an executable radix-2 recursive FFT that exposes the CLRS even/odd split,
  successive twiddle generation, and butterfly layer;
- a theorem that the recursive FFT computes the DFT, together with an inverse
  recursive FFT;
- a generic fixed-capacity FFT polynomial-multiplication pipeline and an
  arbitrary-input complex wrapper, both proved equal to polynomial
  multiplication; and
- execution-attached exact arithmetic counts and `Theta(n log n)` theorems for
  the padded FFT and FFT multiplication.

At closure, Sections 30.1 and 30.2 are `proved`.  Chapter 30 remains `partial`
because Section 30.3's bit-reversal permutation, iterative FFT, butterfly-stage
invariant, and parallel FFT circuit are outside this milestone.

## Scope

### Included

- CLRS third-edition Sections 30.1 and 30.2.
- Pure fixed-length vectors and exact field arithmetic.
- Radix-2 transforms, with padding to the next power of two for arbitrary
  polynomial input sizes.
- A generic characteristic-zero field core parameterized by a primitive root
  of unity.
- CLRS-facing complex wrappers using principal roots of unity.
- Arithmetic-operation costs attached to the executable transform and
  multiplication pipelines.

### Excluded

- Section 30.3 iterative FFT and bit-reverse copy.
- Section 30.3 parallel FFT circuits, circuit depth, and circuit size.
- Mutable arrays, in-place writes, RAM semantics, cache behavior, allocator
  costs, and floating-point roundoff.
- Chapter-end exercises and Problems 30-1 through 30-6.
- Numerical FFT libraries or code generation to an external runtime.

The exclusions are not implicit omissions.  They must appear in the chapter
guide, proof map, progress data, and reader-facing status page.

## Lessons Carried Forward From Chapter 27

This milestone follows four constraints learned during the Chapter 27 attack:

1. A recurrence is not an algorithm runtime until a theorem connects it to an
   execution of the advertised algorithm.
2. An equivalent library transform does not replace the central textbook
   algorithm.  The recursive FFT must expose the even/odd split and butterfly
   recurrence.
3. Power-of-two closed forms alone do not justify an all-input asymptotic claim.
   Padding and adjacent-power bounds must connect arbitrary positive sizes to
   the radix-2 execution.
4. Chapter-sized files should be aggregators over focused definition,
   correctness, and cost modules.

## Algebraic Boundary

The reusable core is parameterized by a field `K` with `CharZero K`.  A forward
DFT of length `n` takes an element `omega : K` together with
`IsPrimitiveRoot omega n`.  Characteristic zero guarantees that a positive
natural transform length has nonzero scalar image, so inverse scaling by
`(n : K)⁻¹` is valid.

The DFT itself is defined for any positive length.  The executable recursive
FFT is specialized to lengths `2 ^ k`.  Its correctness theorem assumes that
`omega` is a primitive `2 ^ k`-th root.  Recursive calls use `omega ^ 2`; a
proved root-reduction lemma supplies the primitive-root certificate at the
smaller length.

The complex public wrapper chooses

```text
exp (2 * pi * I / n)
```

as the principal root, using Mathlib's primitive-root theorem.  This wrapper is
mathematical exact-complex computation.  It may be `noncomputable` because the
principal complex root uses analytic constants; the generic FFT kernel remains
a pure executable function once field operations and a root are supplied.

The core is not generalized to positive-characteristic fields in this
milestone.  Such a generalization would replace `CharZero K` with an explicit
invertibility premise on the transform length and belongs with a future
number-theoretic FFT bridge.

## Representation Boundary

The mathematical and algorithmic representations are deliberately separate:

```lean
abbrev CoeffVector (K : Type*) (n : Nat) := Fin n -> K
abbrev PowTwoVec (K : Type*) (k : Nat) := CoeffVector K (2 ^ k)
```

`Polynomial K` is the mathematical owner of polynomial equality,
multiplication, degree, coefficients, and evaluation.  `CoeffVector K n` is the
fixed-capacity algorithm representation.  It makes DFT sums and index maps
total and removes runtime length errors without hiding a failed precondition in
`Option`.

The bridge consists of:

- `coeffVector n p`, which reads the first `n` coefficients and therefore
  performs zero padding automatically;
- `vectorToPolynomial a`, the finite sum of coefficient monomials;
- coefficient round-trip theorems for every vector position; and
- a polynomial round-trip theorem under an explicit degree-bound premise.

Point-value representations use a sampling function `points : Fin n -> K` and
the vector `fun i => p.eval (points i)`.  General interpolation in Section 30.1
uses injective sample points.  Roots-of-unity sampling is introduced only in
Section 30.2.

## Module Layout

```text
CLRSLean/Chapter_30.lean

CLRSLean/Chapter_30/
  Section_30_1_Representing_Polynomials.lean
  Section_30_1_Representing_Polynomials/
    S1_CoefficientVectors.lean
    S2_PointValueInterpolation.lean
    S3_RepresentationOperations.lean

  Section_30_2_DFT_And_FFT.lean
  Section_30_2_DFT_And_FFT/
    S1_RootsOfUnity.lean
    S2_DFT.lean
    S3_InversionAndConvolution.lean
    RecursiveFFT/
      Definitions.lean
      Correctness.lean
      Costs.lean
    PolynomialMultiplication.lean
```

The two section files are aggregators and reader guides.  Definitions,
correctness, and costs remain in focused submodules, normally below roughly 400
lines each.  A proof stack that exceeds that size is split at a genuine theorem
dependency, not at an arbitrary line count.

Section 30.2 imports Section 30.1.  Section 30.1 never imports Section 30.2.
The final FFT multiplication theorem lives in Section 30.2 because it closes
the representation-level multiplication scheme using results developed later
in the textbook.

All declarations live in `CLRS.Chapter30`.

## Section 30.1: Coefficient Representation

### Polynomial bridge

`S1_CoefficientVectors.lean` defines the fixed-capacity representation and the
conversion functions.  Its public theorem family includes:

- `vectorToPolynomial_coeff`;
- `coeffVector_vectorToPolynomial`;
- `vectorToPolynomial_coeffVector` under the polynomial degree bound; and
- the natural degree/support bound for `vectorToPolynomial`.

The polynomial round trip must be extensional equality in `Polynomial K`, not
only equality at selected sample points.

### Horner evaluation

The file also defines an executable Horner fold over the fixed coefficient
range.  The main theorem

```text
hornerEval_correct
```

states that it equals evaluation of `vectorToPolynomial`.  The cost interface
records a linear number of additions and multiplications in the declared
capacity.  Leading zero padding is intentionally charged: the metric is for the
fixed-capacity algorithm, not a hidden sparse-polynomial optimization.

## Section 30.1: Point-Value Representation

`S2_PointValueInterpolation.lean` defines point-value extraction at a finite
family of sample points.  It reuses Mathlib's Lagrange/interpolation and
finite-root infrastructure rather than reproving general polynomial root
counting.

The public boundary includes:

- `pointValues_injective`: two degree-`< n` polynomials agreeing at `n`
  injectively indexed sample points are equal;
- `interpolate_pointValues`: interpolation recovers the requested value at
  every sample point;
- `interpolate_unique`: the interpolating polynomial is unique under the
  degree bound; and
- a round-trip theorem for interpolation after point-value extraction.

Existence and uniqueness are separate results so later DFT inversion can be
used without unfolding the general interpolation construction.

## Section 30.1: Representation Operations

`S3_RepresentationOperations.lean` proves the operation semantics that motivate
the FFT:

- coefficient-vector addition reconstructs polynomial addition;
- pointwise addition reconstructs polynomial addition;
- pointwise multiplication gives the sample values of polynomial
  multiplication;
- schoolbook coefficient convolution reconstructs polynomial multiplication;
  and
- capacity/degree lemmas state when the product fits without truncation.

The public theorem names include:

- `pointValues_add`;
- `pointValues_mul`;
- `schoolbookMul_correct`; and
- `schoolbookMul_degreeBound`.

The attached arithmetic model records linear work for fixed-capacity addition
and pointwise multiplication and quadratic work for schoolbook multiplication.
These are comparison baselines, not RAM-cost claims.

## Section 30.2: Roots Of Unity

`S1_RootsOfUnity.lean` provides the exact algebraic facts consumed by DFT and
FFT proofs.  Its headline theorem families are:

- `primitiveRoot_powers_injective`, for distinct powers below the order;
- `primitiveRoot_square`, reducing a primitive `2 * n`-th root to a primitive
  `n`-th root;
- `primitiveRoot_half_pow_eq_neg_one`, for the upper-half butterfly sign;
- `root_sum_orthogonality`, evaluating the finite sum of powers as the length
  or zero according to the exponent modulo the order; and
- primitive-root preservation under inversion.

The orthogonality theorem is the shared algebraic kernel for Fourier inversion
and convolution.  It must expose the exact modular condition rather than only
the special case needed by one downstream proof.

## Section 30.2: DFT, Inversion, And Convolution

### DFT convention

`S2_DFT.lean` defines the CLRS-sign forward transform

```text
dft omega a k = sum j, a j * omega ^ (j * k)
```

and proves that it is the point-value vector of the coefficient polynomial at
successive powers of `omega`.

`S3_InversionAndConvolution.lean` defines the inverse transform by applying the
forward sum with `omega⁻¹` and scaling by `(n : K)⁻¹`.  The public boundary
includes:

- `dft_eq_pointValues`;
- `idft_dft`;
- `dft_idft`;
- `dft_injective`;
- `dft_cyclicConvolution`, showing that DFT turns cyclic convolution into
  pointwise multiplication;
- `idft_pointwiseMul`, the inverse-direction form used by FFT polynomial
  multiplication; and
- a no-wrap lemma turning cyclic convolution into ordinary coefficient
  convolution under an explicit capacity bound.

A complex compatibility theorem aligns the CLRS-sign transform with
Mathlib's `ZMod.dft`, accounting explicitly for Mathlib's negative-sign
convention.  This theorem is a compatibility bridge and not the proof of the
generic inversion result.

## Recursive FFT

### Actual control structure

`RecursiveFFT/Definitions.lean` defines:

- `evenCoeffs` and `oddCoeffs`, which read positions `2 * i` and `2 * i + 1`;
- `twiddlePowers`, which produces successive twiddles by carrying a current
  value and multiplying by `omega`;
- `butterflyLayer`, which produces both `u + w * v` and `u - w * v`; and
- `recursiveFFTExec`, which makes two recursive calls with `omega ^ 2` and
  combines their values with one butterfly layer.

The canonical execution object contains the output vector and arithmetic
counters.  `recursiveFFT` is its value projection.  There is no independent
recurrence-only implementation, so the cost cannot drift away from the
algorithm.

The definition must not compute every twiddle as a fresh exponentiation while
charging it as a constant operation.  The successive-twiddle generator is part
of both the value computation and the cost record.

### Correctness invariant

`RecursiveFFT/Correctness.lean` proves the polynomial split identity

```text
A(x) = A_even(x^2) + x * A_odd(x^2)
```

and the two butterfly output identities.  Recursive correctness then proves,
for every output index, that the algorithm computes the corresponding DFT
sum.

The headline theorem is:

```text
recursiveFFT_eq_dft
```

Its premises are only the field/characteristic assumptions and the
primitive-root certificate.  It may not assume that the recursive calls are
already correct through an external certificate; that fact must arise from the
structural induction.

The inverse algorithm runs the same recursive kernel with `omega⁻¹` and then
scales every output by `(2 ^ k : K)⁻¹`.  Its public theorems are:

- `recursiveIFFT_eq_idft`; and
- `recursiveIFFT_recursiveFFT` and `recursiveFFT_recursiveIFFT`, the two
  round-trip directions.

## Arithmetic-Cost Model

The milestone counts exact field arithmetic, not wall-clock time or RAM
instructions.  Each butterfly iteration charges:

- one multiplication for `w * v`;
- one addition and one subtraction;
- one multiplication for the next twiddle.

The final twiddle update is charged because it is performed by the declared
loop, even though the next value is not consumed.  At size `2 ^ (k + 1)`, the
current level therefore charges `2 * 2 ^ (k + 1)` arithmetic operations.

With `W 0 = 0`, the exact recurrence and closed form are:

```text
W (k + 1) = 2 * W k + 2 * 2 ^ (k + 1)
W k       = 2 * k * 2 ^ k
```

`RecursiveFFT/Costs.lean` proves:

- `recursiveFFTExec_value`, the erasure/refinement theorem;
- exact multiplication and addition/subtraction counter equations;
- `recursiveFFTWork_exact`;
- the exact-power `Theta(n log n)` wrapper; and
- `paddedFFTWork_allInput_bigTheta`, using the repository's adjacent-power
  transfer infrastructure.

The asymptotic theorem is not proved about a detached recurrence.  A public
equation identifies the work field of every execution with the analyzed cost
function.

## FFT Polynomial Multiplication

`PolynomialMultiplication.lean` defines the generic pipeline:

```text
p, q
  -> zero-padded coefficient vectors
  -> two recursive FFT executions
  -> pointwise multiplication
  -> recursive inverse FFT
  -> polynomial reconstruction
```

The generic operation takes a radix exponent, a primitive root, and explicit
degree/capacity proofs.  The main theorem

```text
fftMultiplyAt_correct
```

states equality with `p * q` in `Polynomial K`.  The proof composes the FFT
correctness theorem, DFT pointwise multiplication, no-wrap convolution, inverse
correctness, and coefficient reconstruction.

The complex wrapper computes a positive input bound from both polynomial
supports, chooses a power-of-two capacity large enough for their product,
constructs the corresponding principal root, and invokes the generic pipeline.
Its headline theorem is:

```text
complexFFTMultiply_correct
```

This theorem is unconditional for all complex polynomials, including zero and
constant polynomials.

The multiplication execution record includes both forward transforms, the
pointwise product, inverse transform, and inverse scaling.  Its numeric cost is
deterministic for a declared input bound.  The public cost boundary includes:

- an exact composition equation for the multiplication work;
- a theorem connecting the execution's work field to that equation; and
- `fftMultiplyWork_allInput_bigTheta`, proving `Theta(n log n)` after automatic
  next-power-of-two padding.

The all-input proof records the positive-size convention explicitly and uses a
fixed coefficient-capacity input size, so zero coefficients do not silently
change the advertised cost universe.

## Error And Edge-Case Handling

- Transform vectors are nonempty because their size is `2 ^ k`.
- Generic DFT inversion states positivity or a `NeZero` instance for arbitrary
  transform length.
- A generic FFT root need not be checked dynamically; correctness is
  conditional on `IsPrimitiveRoot`.
- Insufficient multiplication capacity is a theorem premise, not an `Option`
  failure with a junk result.
- The complex wrapper constructs enough capacity and discharges this premise
  internally.
- Size one, zero polynomial, constant polynomial, leading-zero padding, and a
  product reaching the last legal coefficient are covered by focused examples.

## Public Test Design

The milestone adds:

```text
Tests/Chapter_30_Interface.lean
Tests/Chapter_30_DFT_Interface.lean
Tests/Chapter_30_RecursiveFFT_Interface.lean
Tests/Chapter_30_PolynomialMultiplication_Interface.lean
Tests/Chapter_30_Milestone1_Closure.lean
```

`Chapter_30_Interface.lean` checks the stable representation and aggregator
surface.  The three focused tests check the DFT/inversion, executable recursive
FFT, and multiplication/cost families.  Small examples cover:

- zero and constant polynomials;
- transform lengths one, two, and four;
- explicit zero padding;
- internal and leading zero coefficients;
- inverse-after-forward round trips; and
- a polynomial product whose highest nonzero coefficient reaches the last
  allowed output position.

Examples use exact algebraic values and proved root certificates.  They do not
rely on approximate complex-number evaluation.

`Chapter_30_Milestone1_Closure.lean` imports only `CLRSLean.Chapter_30`, checks
at least one headline theorem from every acceptance group, and prints axioms
for:

- point-value uniqueness;
- Fourier inversion;
- recursive FFT correctness;
- recursive inverse correctness;
- generic FFT multiplication correctness;
- arbitrary-input complex multiplication correctness;
- execution refinement; and
- both all-input `Theta(n log n)` theorems.

Only repository-accepted logical dependencies such as `propext`,
`Classical.choice`, and `Quot.sound` may appear.  `sorryAx` and project-defined
axioms are forbidden.

## Documentation And Status

The milestone wires the new chapter through all live owners:

- `CLRSLean.lean` imports `CLRSLean.Chapter_30`;
- `literate.toml` registers the chapter, both section aggregators, and every
  theorem-bearing child module in dependency order;
- `CLRSLean/Chapter_30.lean` states the represented boundary and names Section
  30.3 as the single main-text gap;
- `CLRSLean/Status.lean` lists Chapter 30 under structured-but-partial chapters;
- `docs/proof-map.md` records the theorem interface and exact cost model;
- `docs/clrs-proof-progress.csv` changes Chapter 30 from `not-started` to
  `partial`, represents `30.1;30.2`, and names Section 30.3 as the remaining
  core group;
- `CLRSLean/Progress.lean` and the README table are regenerated from the CSV;
- `docs/proof-status-board.md` records the next Chapter 30 target only if the
  repository's active priority list is updated; and
- `docs/index.md` registers every new source and the dated milestone audit.

The progress count follows the repository theorem-group policy after the public
interfaces compile.  Compatibility bridges, exact erasure equations, and
aliases do not inflate the count.

## Verification Boundary

Development uses focused checks after each module and interface test.  The
milestone closure gate is:

```text
lake env lean Tests/Chapter_30_Interface.lean
lake env lean Tests/Chapter_30_DFT_Interface.lean
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_30 -g '*.lean'
uv run python scripts/check_repository.py
uv run python scripts/check_site_consistency.py
git diff --check
lake build CLRSLean
lake build :literateHtml
```

The unfinished-proof scan must have no matches.  Every command must exit zero,
and the closure test's axiom output must be inspected rather than inferred from
the build result.

## Rejected Alternatives

### Mathlib `ZMod.dft` as the core specification

Mathlib's transform supplies a valuable complex-linear equivalence and
inversion theorem, but using it as the sole core would conflict with the
approved generic characteristic-zero field boundary.  It remains a complex
compatibility bridge.

### Vandermonde-matrix-first proof

Vandermonde invertibility gives an elegant interpolation proof, but a matrix
factorization would move the main burden into block permutations and obscure
the CLRS recursive algorithm.  General interpolation may reuse Mathlib's
Vandermonde/Lagrange facts; recursive FFT correctness remains an even/odd and
butterfly proof.

### Defining FFT as DFT

This would make correctness definitional while omitting the chapter's central
divide-and-conquer algorithm and recurrence.  It is not an acceptable
formalization of Section 30.2.

### Fresh exponentiation for every twiddle

Computing `omega ^ j` independently at each output while charging one
multiplication would make the value algorithm and cost semantics disagree.
Successive twiddle generation is therefore part of the execution.

### Mutable arrays in milestone 1

Array updates and disjoint-write invariants belong to Section 30.3's iterative
implementation.  Introducing them into recursive FFT would increase proof
surface without strengthening the agreed Section 30.2 theorem.

### Exact powers without padded all-input theorems

An exact `2 ^ k` recurrence is necessary but does not by itself prove the
advertised arbitrary-size multiplication bound.  The milestone includes
next-power-of-two padding and adjacent-power transfer.

## Acceptance Criteria

Milestone 1 is complete only when all of the following hold:

1. Coefficient vectors and `Polynomial K` have proved coefficient and
   polynomial round trips under the exact capacity condition.
2. Horner evaluation, point-value extraction, interpolation uniqueness,
   pointwise operations, and schoolbook multiplication have public correctness
   theorems and honest arithmetic-cost boundaries.
3. Primitive-root powers, squaring, inversion, half-power negation, and finite
   orthogonality are proved in the generic field model.
4. Generic DFT and inverse DFT are mutual inverses, and DFT converts cyclic
   convolution to pointwise multiplication.
5. `recursiveFFTExec` exposes even/odd recursion, successive twiddles, and
   butterflies; its value is proved equal to DFT without a certificate that
   assumes recursive correctness.
6. Recursive inverse FFT is proved equal to inverse DFT and is a left and right
   inverse of recursive FFT under the primitive-root premise.
7. The generic fixed-capacity FFT multiplication pipeline and arbitrary-input
   complex wrapper are both proved equal to polynomial multiplication,
   including zero and constant inputs.
8. The recursive FFT execution has exact field-operation counts and an
   execution-connected `Theta(n log n)` result; padded FFT and complete
   multiplication have all-input `Theta(n log n)` theorems.
9. All focused interfaces, closure tests, repository checks, root-library
   build, and literate-site build pass without unfinished proofs or
   nonstandard axioms.
10. Sections 30.1 and 30.2 are consistently recorded as proved, Chapter 30 is
    consistently recorded as partial, and Section 30.3 is the only named
    remaining main-text proof group.
