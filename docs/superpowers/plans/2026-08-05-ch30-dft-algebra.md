# Chapter 30 DFT Algebra Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize roots-of-unity algebra, the generic CLRS-sign DFT and inverse, Fourier inversion, cyclic convolution, no-wrap polynomial convolution, and the complex compatibility bridge needed by the recursive FFT and multiplication plans.

**Architecture:** The reusable transform is a finite sum on `Fin n → K` over a characteristic-zero field.  A single modular orthogonality theorem supplies inversion and convolution; Mathlib's complex `ZMod.dft` is connected only through a sign-aware compatibility theorem and is not used as the generic specification.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `IsPrimitiveRoot`, `ZMod`, finite Fourier, `Polynomial`, `Finset`, Lake, Verso, CLRS-Lean interface tests.

---

## Prerequisite

Complete `docs/superpowers/plans/2026-08-05-ch30-representations.md` first.  Its Chapter 30 aggregator and `CoeffVector` API are the only upstream Chapter 30 dependencies.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity.lean` for the primitive-root toolkit and orthogonality.
- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT.lean` for DFT, power-point sampling, and the complex compatibility bridge.
- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution.lean` for inverse DFT, inversion, cyclic convolution, and no-wrap results.
- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean` as the evolving Section 30.2 aggregator and reader guide.
- Create `Tests/Chapter_30_DFT_Interface.lean` for the stable algebraic surface and exact transforms of lengths one, two, and four.
- Modify `CLRSLean/Chapter_30.lean`, `literate.toml`, and `docs/index.md` to expose and register the DFT modules without updating completion status.

### Task 1: Lock the DFT Surface in RED

**Files:**
- Create: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Add the public interface contract**

Create the test importing only `CLRSLean.Chapter_30`:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check primitiveRoot_powers_injective
#check primitiveRoot_square
#check primitiveRoot_half_pow_eq_neg_one
#check primitiveRoot_inv
#check root_sum_orthogonality
#check powerPoints
#check dft
#check dft_eq_pointValues
#check complexDft_mathlib
#check idft
#check idft_dft
#check dft_idft
#check dft_injective
#check cyclicSub
#check cyclicConvolution
#check dft_cyclicConvolution
#check idft_pointwiseMul
#check cyclicConvolution_eq_coeffVector_mul

end CLRS.Chapter30
```

- [ ] **Step 2: Verify the expected RED failure**

Run:

```bash
lake env lean Tests/Chapter_30_DFT_Interface.lean
```

Expected: nonzero exit with the first unknown roots-of-unity declaration.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_30_DFT_Interface.lean
git commit -m "test(ch30): specify DFT algebra interface"
```

### Task 2: Build the Primitive-Root Toolkit

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity.lean`
- Test: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Inspect and pin the Mathlib facts used by the proofs**

Run:

```bash
rg -n 'theorem (pow|pow_inj|inv|eq_neg_one_of_two_right|geom_sum_eq_zero)' \
  .lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean
rg -n 'isPrimitiveRoot_exp' \
  .lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/Complex.lean
```

Expected: find `IsPrimitiveRoot.pow`, `pow_inj`, `inv`, `eq_neg_one_of_two_right`, `geom_sum_eq_zero`, and `Complex.isPrimitiveRoot_exp`.  Use these facts rather than reproving order theory.

- [ ] **Step 2: Prove injectivity of the first `n` powers**

Import Mathlib's primitive-root and complex roots modules, then add:

```lean
theorem primitiveRoot_powers_injective [CommRing K] {n : Nat} {omega : K}
    (homega : IsPrimitiveRoot omega n) :
    Function.Injective (fun i : Fin n => omega ^ i.1) := by
  intro i j hij
  apply Fin.ext
  exact homega.pow_inj i.2 j.2 hij
```

Retain the `Fin n` domain: later interpolation uses exactly this injective sampling family.

- [ ] **Step 3: Prove the radix-2 root reductions**

Add the square and inverse wrappers:

```lean
theorem primitiveRoot_square [CommMonoid K] {n : Nat} {omega : K}
    (hn : 0 < n) (homega : IsPrimitiveRoot omega (2 * n)) :
    IsPrimitiveRoot (omega ^ 2) n := by
  exact homega.pow (by omega) rfl

theorem primitiveRoot_inv [CommGroupWithZero K] {n : Nat} {omega : K}
    (homega : IsPrimitiveRoot omega n) :
    IsPrimitiveRoot omega⁻¹ n := homega.inv
```

Check the factor orientation expected by `IsPrimitiveRoot.pow`; normalize `2 ^ (k + 1)` with `pow_succ` only in downstream wrappers.

- [ ] **Step 4: Prove the half-power sign theorem**

For a field of characteristic zero and positive `n`, prove:

```lean
theorem primitiveRoot_half_pow_eq_neg_one [Field K] [CharZero K]
    {n : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega (2 * n)) :
    omega ^ n = -1 := by
  have htwo : IsPrimitiveRoot (omega ^ n) 2 := by
    exact homega.pow (by omega) (by omega)
  exact htwo.eq_neg_one_of_two_right
```

Use the Mathlib lemma rather than deriving the two roots of `X^2 - 1` manually.

- [ ] **Step 5: Prove modular root-sum orthogonality**

Expose the complete case split needed by both inversion and convolution:

```lean
theorem root_sum_orthogonality [Field K] [CharZero K]
    {n exponent : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega n) :
    (∑ j : Fin n, omega ^ (j.1 * exponent)) =
      if n ∣ exponent then (n : K) else 0 := by
  by_cases hdiv : n ∣ exponent
  · obtain ⟨t, rfl⟩ := hdiv
    simp [pow_mul, homega.pow_eq_one]
  · have hprimitive : IsPrimitiveRoot (omega ^ exponent) (n / n.gcd exponent) :=
      -- Derive with the appropriate `IsPrimitiveRoot.pow`/coprime theorem.
    have horder : 1 < n / n.gcd exponent := by
      -- `hdiv` rules out quotient one.
    simpa [pow_mul] using hprimitive.geom_sum_eq_zero horder
```

The internal proof may instead use `geom_sum_mul` plus `homega.pow_eq_one_iff_dvd` if that is shorter.  The public result must retain the exact `n ∣ exponent` condition and `(n : K)` branch.

- [ ] **Step 6: Add the signed/difference orthogonality corollary**

Prove a form over `i k : Fin n` that evaluates
`∑ j, omega ^ (j * i) * omega⁻¹ ^ (j * k)` to `(n : K)` when `i = k` and zero otherwise.  Use integer exponents or a modular subtraction helper rather than an invalid natural subtraction rewrite when `i < k`.  This corollary is the direct kernel for `idft_dft`.

- [ ] **Step 7: Verify and commit the roots module**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S1_RootsOfUnity
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity.lean
```

Expected: build exit 0 and no scan matches.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S1_RootsOfUnity.lean
git commit -m "feat(ch30): prove roots-of-unity orthogonality"
```

### Task 3: Define the Generic CLRS-Sign DFT

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT.lean`
- Test: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Define power points and the transform**

Import S1 and the Section 30.1 polynomial bridge:

```lean
def powerPoints [Monoid K] {n : Nat} (omega : K) : Fin n → K :=
  fun k => omega ^ k.1

def dft [Semiring K] {n : Nat} (omega : K) (a : CoeffVector K n) :
    CoeffVector K n :=
  fun k => ∑ j : Fin n, a j * omega ^ (j.1 * k.1)
```

The forward sign is positive, matching the CLRS convention fixed by the design.

- [ ] **Step 2: Prove that DFT is point-value evaluation**

Add:

```lean
theorem dft_eq_pointValues [CommSemiring K] {n : Nat}
    (omega : K) (a : CoeffVector K n) :
    dft omega a = pointValues (powerPoints omega) (vectorToPolynomial a) := by
  funext k
  simp [dft, pointValues, powerPoints, vectorToPolynomial,
    Polynomial.eval_finset_sum, pow_mul]
```

If the simplifier needs explicit distribution over the finite polynomial sum, prove an `eval_vectorToPolynomial` helper first and use it here.

- [ ] **Step 3: Record linearity and small exact transforms**

Prove `dft_zero`, `dft_add`, and `dft_smul` over the weakest correct algebraic assumptions.  Add exact tests for:

- length one with root `1`;
- length two with root `-1` over `ℚ`; and
- length four over `ℂ` using `Complex.I` or the chosen principal root with a proved primitive-root certificate.

The tests should compare finite vectors extensionally, not compare approximate complex values.

- [ ] **Step 4: Verify and commit the generic DFT**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S2_DFT
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT.lean \
  Tests/Chapter_30_DFT_Interface.lean
git commit -m "feat(ch30): define generic discrete Fourier transform"
```

### Task 4: Add the Complex Mathlib Compatibility Bridge

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT.lean`
- Test: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Inspect Mathlib's exact index and sign convention**

Run:

```bash
sed -n '90,190p' .lake/packages/mathlib/Mathlib/Analysis/Fourier/ZMod.lean
sed -n '35,58p' .lake/packages/mathlib/Mathlib/Data/ZMod/Basic.lean
```

Expected: confirm that `ZMod.dft` uses `ZMod N → ℂ`, its kernel carries the negative exponential sign, and `ZMod.finEquiv` transports `Fin N` to `ZMod N` under `[NeZero N]`.

- [ ] **Step 2: Define the transport helpers explicitly**

Add private or documented helpers translating vectors along `ZMod.finEquiv`.  Name both directions and prove round trips before stating Fourier compatibility.  Do not hide a sign reversal in a broad `simp` call.

- [ ] **Step 3: Prove the compatibility theorem**

State `complexDft_mathlib` so its left side is the generic `dft` at the positive-sign principal root and its right side is Mathlib's transform with either the output index negated or the inverse principal root.  The statement must visibly account for the sign, for example:

```lean
theorem complexDft_mathlib {n : Nat} [NeZero n]
    (a : CoeffVector ℂ n) (k : Fin n) :
    dft (Complex.exp (2 * Real.pi * Complex.I / n)) a k =
      ZMod.dft (finVectorToZMod a) (-(ZMod.finEquiv n k)) := by
  -- Expand both transforms, reindex with `ZMod.finEquiv`, and normalize
  -- `exp` exponents; inspect the exact Mathlib argument order before fixing
  -- the final theorem spelling.
```

It is acceptable to adjust the right-side application syntax to the installed Mathlib signature.  It is not acceptable to change the generic DFT sign or replace the theorem with an uncited assertion of equivalence.

- [ ] **Step 4: Verify and commit the bridge**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S2_DFT
lake env lean Tests/Chapter_30_DFT_Interface.lean
```

At this point the focused interface may still fail on inverse/convolution names, but S2 itself must build and the compatibility theorem must elaborate.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S2_DFT.lean
git commit -m "feat(ch30): bridge generic and Mathlib complex DFTs"
```

### Task 5: Prove Fourier Inversion

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution.lean`
- Test: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Define inverse DFT from the same forward sum**

Import S2 and define:

```lean
def idft [Field K] {n : Nat} (omega : K) (a : CoeffVector K n) :
    CoeffVector K n :=
  fun k => (n : K)⁻¹ * dft omega⁻¹ a k
```

The inverse uses the inverse root plus scalar normalization.  Keep positivity/primitive-root assumptions on theorems rather than storing proofs in the value.

- [ ] **Step 2: Prove scalar nonvanishing from characteristic zero**

Add a local helper:

```lean
theorem natCast_ne_zero_of_pos [Field K] [CharZero K] {n : Nat} (hn : 0 < n) :
    (n : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
```

Reuse it wherever inverse scaling cancels.  Do not add an axiom or a stronger algebraic typeclass than needed.

- [ ] **Step 3: Prove both inversion directions**

Add:

```lean
theorem idft_dft [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n) (a : CoeffVector K n) :
    idft omega (dft omega a) = a := by
  funext k
  -- Expand both sums, interchange `Finset.univ` sums, apply signed
  -- orthogonality, and cancel `(n : K)⁻¹ * n`.

theorem dft_idft [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n) (a : CoeffVector K n) :
    dft omega (idft omega a) = a := by
  -- Apply `idft_dft` to `omega⁻¹`, using `primitiveRoot_inv`, then normalize
  -- the two inverse-root occurrences; alternatively repeat orthogonality.

theorem dft_injective [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n) :
    Function.Injective (dft omega : CoeffVector K n → CoeffVector K n) := by
  intro a b h
  calc
    a = idft omega (dft omega a) := (idft_dft hn homega a).symm
    _ = idft omega (dft omega b) := congrArg (idft omega) h
    _ = b := idft_dft hn homega b
```

- [ ] **Step 4: Add exact round-trip examples**

Exercise sizes one, two, and four, including a vector with internal zeros.  Include both `idft (dft a) = a` and `dft (idft a) = a` examples through the public theorems.

### Task 6: Prove Cyclic Convolution and No-Wrap Semantics

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution.lean`
- Test: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Define total modular subtraction and cyclic convolution**

Avoid relying on an ambiguous `Fin` subtraction instance:

```lean
def cyclicSub {n : Nat} (hn : 0 < n) (k j : Fin n) : Fin n :=
  ⟨(k.1 + n - j.1) % n, Nat.mod_lt _ hn⟩

def cyclicConvolution [Semiring K] {n : Nat} (hn : 0 < n)
    (a b : CoeffVector K n) : CoeffVector K n :=
  fun k => ∑ j : Fin n, a j * b (cyclicSub hn k j)
```

Prove helper lemmas characterizing `cyclicSub` as modular addition and showing the relevant reindexing maps are permutations of `Fin n`.

- [ ] **Step 2: Prove the convolution theorem**

Add:

```lean
theorem dft_cyclicConvolution [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n)
    (a b : CoeffVector K n) :
    dft omega (cyclicConvolution hn a b) =
      pointwiseMul (dft omega a) (dft omega b) := by
  funext k
  -- Expand, reindex the cyclic subtraction, distribute sums, and reduce
  -- exponents modulo `n` using `homega.pow_eq_one`.
```

Then derive the inverse-facing form used by multiplication:

```lean
theorem idft_pointwiseMul [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n)
    (a b : CoeffVector K n) :
    idft omega (pointwiseMul (dft omega a) (dft omega b)) =
      cyclicConvolution hn a b := by
  rw [← dft_cyclicConvolution hn homega, idft_dft hn homega]
```

- [ ] **Step 3: Prove the no-wrap polynomial bridge**

State a theorem in terms of the product fitting into capacity `n`:

```lean
theorem cyclicConvolution_eq_coeffVector_mul [Field K] {n : Nat} (hn : 0 < n)
    (p q : K[X]) (hfit : (p * q).degree < n) :
    cyclicConvolution hn (coeffVector n p) (coeffVector n q) =
      coeffVector n (p * q) := by
  funext k
  -- Expand polynomial multiplication coefficients.  Use `hfit` to show that
  -- every wrapped index contributes zero and identify the unwrapped terms.
```

If the coefficient proof is substantially cleaner from explicit support bounds on `p` and `q`, first prove that stronger helper and retain this degree-based theorem as the public wrapper.

- [ ] **Step 4: Verify the complete DFT interface**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S3_InversionAndConvolution
lake env lean Tests/Chapter_30_DFT_Interface.lean
```

The S3 build must exit 0.  The interface remains RED only until the aggregators are extended in Task 7.

- [ ] **Step 5: Commit inversion and convolution**

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/S3_InversionAndConvolution.lean \
  Tests/Chapter_30_DFT_Interface.lean
git commit -m "feat(ch30): prove Fourier inversion and convolution"
```

### Task 7: Assemble the DFT Algebra Surface

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean`
- Modify: `CLRSLean/Chapter_30.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Status.lean`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`
- Test: `Tests/Chapter_30_DFT_Interface.lean`

- [ ] **Step 1: Create the Section 30.2 aggregator**

Import S1-S3 in order.  Its guide must distinguish the generic field core from the complex compatibility theorem and explicitly say that recursive FFT and FFT multiplication are added by the next plans.

- [ ] **Step 2: Extend the chapter aggregator**

Add:

```lean
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT
```

Update the reader guide to list the DFT/inversion/convolution results without claiming the recursive algorithm exists yet.

- [ ] **Step 3: Register the four DFT source modules**

Add the section aggregator and S1-S3 to `literate.toml` in dependency order and to `docs/index.md`.

- [ ] **Step 4: Update the truthful intermediate DFT status**

Extend `docs/proof-map.md` with the completed root/DFT/inversion/convolution groups.  Change the Chapter 30 CSV row to represented sections `30.1;30.2`, keep status `partial`, and use reviewed interface-group counts.  Record two remaining core groups: the recursive FFT/multiplication execution boundary within 30.2, and Section 30.3.  Update the Chapter 30 paragraph in `CLRSLean/Status.lean`, then regenerate:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py
```

Expected: both exit 0 and no status text claims the recursive FFT exists yet.

- [ ] **Step 5: Turn the focused interface GREEN**

Run:

```bash
lake env lean Tests/Chapter_30_DFT_Interface.lean
lake env lean Tests/Chapter_30_Interface.lean
lake build +CLRSLean.Chapter_30
uv run python scripts/check_repository.py
git diff --check
```

Expected: all commands exit 0.

- [ ] **Step 6: Inspect theorem axioms now, before recursive proofs depend on them**

Temporarily add or run `#print axioms` for `root_sum_orthogonality`, `idft_dft`, `dft_idft`, `dft_cyclicConvolution`, and `cyclicConvolution_eq_coeffVector_mul` through a checked test file.

Expected: only repository-accepted logical dependencies; no `sorryAx` and no project-defined axioms.

- [ ] **Step 7: Commit the DFT assembly**

```bash
git add CLRSLean/Chapter_30.lean \
  CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean \
  literate.toml docs/index.md docs/proof-map.md \
  docs/clrs-proof-progress.csv CLRSLean/Status.lean \
  CLRSLean/Progress.lean README.md
git commit -m "feat(ch30): assemble DFT algebra surface"
```

## Plan 2 Acceptance Gate

- [ ] The generic DFT uses positive CLRS exponents and does not depend on `ℂ`.
- [ ] Orthogonality exposes the exact divisibility condition and drives inversion.
- [ ] Both inverse directions and DFT injectivity compile for every positive transform length over a characteristic-zero field.
- [ ] Cyclic convolution is executable and the no-wrap theorem connects it to polynomial coefficients under an explicit capacity premise.
- [ ] The Mathlib compatibility theorem visibly accounts for its negative-sign convention.
- [ ] Exact size-one, size-two, and size-four tests pass without approximate complex evaluation.
- [ ] All DFT modules and focused tests contain no unfinished proofs or project-defined axioms.
