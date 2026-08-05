# Chapter 30 FFT Multiplication and Milestone Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the generic and complex FFT polynomial-multiplication pipelines, attach their exact and all-input costs to execution, seal the Chapter 30 milestone interface, and update every repository status owner so Sections 30.1-30.2 are proved while Section 30.3 remains the single named gap.

**Architecture:** The multiplication execution composes two forward recursive FFT executions, one pointwise product, one inverse-root recursive execution, inverse scaling, and polynomial reconstruction.  Correctness reuses Fourier convolution plus no-wrap capacity; the complex wrapper computes a sufficient power-of-two capacity and principal root internally.  Status changes occur only after focused, closure, repository, root-library, and site gates pass.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `Polynomial`/complex roots-of-unity APIs, CLRS Chapter 3/4 asymptotic infrastructure, Lake, Verso, repository progress generators, interface and axiom-closure tests.

---

## Prerequisite

Complete `docs/superpowers/plans/2026-08-05-ch30-recursive-fft.md` first.  This plan assumes the representation, DFT, inverse/convolution, recursive FFT, exact work, and padding APIs are green.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean` for generic execution, correctness, complex automatic padding, and costs.
- Create `Tests/Chapter_30_PolynomialMultiplication_Interface.lean` for generic, complex, boundary, and work examples.
- Create `Tests/Chapter_30_Milestone1_Closure.lean` for headline theorem checks and axiom output.
- Modify `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean` and `CLRSLean/Chapter_30.lean` to state the final represented boundary.
- Modify `CLRSLean.lean` to expose Chapter 30 from the root library.
- Modify `literate.toml` and `docs/index.md` to register the last source and dated audit.
- Modify `CLRSLean/Status.lean`, `docs/proof-map.md`, `docs/clrs-proof-progress.csv`, and optionally `docs/proof-status-board.md` when the active-priority list changes.
- Regenerate `CLRSLean/Progress.lean` and the generated README progress table.
- Create `docs/proof-audits/chapter-30-milestone-1-2026-08-05.md` as the evidence snapshot.

### Task 1: Lock Multiplication and Closure Contracts in RED

**Files:**
- Create: `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`
- Create: `Tests/Chapter_30_Milestone1_Closure.lean`

- [ ] **Step 1: Add the focused multiplication interface**

Create a test importing only `CLRSLean.Chapter_30` and checking:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check FFTMultiplicationExecution
#check FFTMultiplicationExecution.work
#check scaleVectorExec
#check scaleVectorExec_work_exact
#check fftMultiplyExecAt
#check fftMultiplyAt
#check fftMultiplyExecAt_value
#check fftMultiplyAt_correct
#check polySize
#check multiplicationInputSize
#check complexFFTExponent
#check complexFFTCapacity
#check complexFFTRoot
#check complexFFTMultiply
#check complexFFTMultiply_correct
#check radix2FFTMultiplyWork
#check fftMultiplyExecAt_work_exact
#check fftMultiplyWork
#check fftMultiplyWork_allInput_bigTheta

end CLRS.Chapter30
```

- [ ] **Step 2: Add the milestone closure test**

Create `Tests/Chapter_30_Milestone1_Closure.lean`, importing only `CLRSLean.Chapter_30`.  It must `#check` at least:

```lean
vectorToPolynomial_coeffVector
interpolate_unique
schoolbookMul_correct
root_sum_orthogonality
idft_dft
dft_cyclicConvolution
recursiveFFT_eq_dft
recursiveIFFT_eq_idft
recursiveIFFT_recursiveFFT
fftMultiplyAt_correct
complexFFTMultiply_correct
recursiveFFTExec_value
recursiveFFTWork_exact
paddedFFTWork_allInput_bigTheta
fftMultiplyExecAt_work_exact
fftMultiplyWork_allInput_bigTheta
```

Also add `#print axioms` for:

- `interpolate_unique`;
- `idft_dft`;
- `recursiveFFT_eq_dft`;
- `recursiveIFFT_eq_idft`;
- `fftMultiplyAt_correct`;
- `complexFFTMultiply_correct`;
- `recursiveFFTExec_value`;
- `paddedFFTWork_allInput_bigTheta`; and
- `fftMultiplyWork_allInput_bigTheta`.

- [ ] **Step 3: Verify both tests are RED for the intended reason**

Run:

```bash
lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
```

Expected: both exit nonzero on missing multiplication declarations, not on missing upstream Chapter 30 imports.

- [ ] **Step 4: Commit the RED contracts**

```bash
git add Tests/Chapter_30_PolynomialMultiplication_Interface.lean \
  Tests/Chapter_30_Milestone1_Closure.lean
git commit -m "test(ch30): specify FFT multiplication closure"
```

### Task 2: Implement the Generic Fixed-Capacity Multiplication Execution

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean`
- Test: `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`

- [ ] **Step 1: Define the pipeline execution record**

Import RecursiveFFT Costs and add:

```lean
structure FFTMultiplicationExecution (K : Type*) where
  value : K[X]
  addSubtractions : Nat
  multiplications : Nat

def FFTMultiplicationExecution.work (r : FFTMultiplicationExecution K) : Nat :=
  r.addSubtractions + r.multiplications
```

Document that coefficient reads, finite-index bookkeeping, root-certificate proofs, and polynomial reconstruction are not field arithmetic; both inverse scaling and pointwise products are field multiplications and are charged.

- [ ] **Step 2: Define the generic execution once**

For capacity `N = 2 ^ k`, define:

```lean
def scaleVectorExec [Mul K] {n : Nat} (c : K) (a : CoeffVector K n) :
    VectorArithmeticExecution K n :=
  ⟨fun i => c * a i, 0, n⟩

def fftMultiplyExecAt [Field K] {k : Nat} (omega : K)
    (p q : K[X]) : FFTMultiplicationExecution K :=
  let a := coeffVector (2 ^ k) p
  let b := coeffVector (2 ^ k) q
  let leftRun := recursiveFFTExec omega a
  let rightRun := recursiveFFTExec omega b
  let productRun := pointwiseMulExec leftRun.value rightRun.value
  let inverseRun := recursiveFFTExec omega⁻¹ productRun.value
  let scaleRun := scaleVectorExec ((2 ^ k : Nat) : K)⁻¹ inverseRun.value
  ⟨vectorToPolynomial scaleRun.value,
    leftRun.addSubtractions + rightRun.addSubtractions +
      inverseRun.addSubtractions + productRun.additions + scaleRun.additions,
    leftRun.multiplications + rightRun.multiplications +
      inverseRun.multiplications + productRun.multiplications +
      scaleRun.multiplications⟩

def fftMultiplyAt [Field K] {k : Nat} (omega : K)
    (p q : K[X]) : K[X] :=
  (fftMultiplyExecAt omega p q).value
```

Prove `scaleVectorExec_work_exact` immediately after the definition.  The final `2 * 2 ^ k` charge is then read from `productRun` and `scaleRun`: `2 ^ k` pointwise products plus `2 ^ k` inverse-scale products.  The inverse recursive execution uses `omega⁻¹`, exactly as `recursiveIFFT` does.

- [ ] **Step 3: Add the public erasure equation**

```lean
theorem fftMultiplyExecAt_value [Field K] {k : Nat} (omega : K)
    (p q : K[X]) :
    (fftMultiplyExecAt omega p q).value = fftMultiplyAt omega p q := rfl
```

- [ ] **Step 4: Prove the execution value is the semantic pipeline**

Before polynomial correctness, prove a vector-level equation rewriting the scaled inverse execution as:

```text
idft omega (pointwiseMul (dft omega (coeffVector N p))
                         (dft omega (coeffVector N q)))
```

Use `recursiveFFT_eq_dft` for both forward runs and `recursiveIFFT_eq_idft` for the inverse-root run plus scaling.  This helper prevents counter fields from leaking into the algebraic proof.

- [ ] **Step 5: Compile the generic implementation**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.PolynomialMultiplication
```

Expected: exit 0 with the definitions and semantic-pipeline helper.

### Task 3: Prove Generic FFT Multiplication Correctness

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean`
- Test: `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`

- [ ] **Step 1: State the exact capacity theorem**

Add:

```lean
theorem fftMultiplyAt_correct [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (p q : K[X]) (hfit : (p * q).degree < 2 ^ k) :
    fftMultiplyAt omega p q = p * q := by
  -- Rewrite the execution value to the semantic DFT pipeline.
  -- Apply `idft_pointwiseMul`.
  -- Apply `cyclicConvolution_eq_coeffVector_mul hfit`.
  -- Finish with `vectorToPolynomial_coeffVector hfit`.
```

The theorem's only algorithmic precondition is that the product fits in the declared capacity.  Do not return `Option`, silently truncate, or require the caller to provide an interpolated result.

- [ ] **Step 2: Add support-bound convenience wrappers**

Prove a corollary accepting `p.degree < m`, `q.degree < n`, and `m + n ≤ 2 ^ k`, deriving `hfit` with Mathlib's degree-of-product bound.  Keep `fftMultiplyAt_correct` as the headline theorem because it states the minimal no-wrap condition.

- [ ] **Step 3: Add exact generic examples**

Over `ℚ`, use the primitive second root `-1` to cover constant/linear inputs.  Over `ℂ`, use a primitive fourth root for `(1 + X) * (1 - X)` or another exact degree-two product.  Include a case whose highest nonzero product coefficient is at index `N - 1` to prove the boundary is strict and nontruncating.

- [ ] **Step 4: Verify and commit generic correctness**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.PolynomialMultiplication
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean \
  Tests/Chapter_30_PolynomialMultiplication_Interface.lean
git commit -m "feat(ch30): prove generic FFT polynomial multiplication"
```

### Task 4: Implement the Arbitrary-Input Complex Wrapper

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean`
- Test: `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`

- [ ] **Step 1: Define a positive coefficient-size convention**

```lean
def polySize {K : Type*} [Semiring K] (p : K[X]) : Nat :=
  p.natDegree + 1

def multiplicationInputSize {K : Type*} [Semiring K] (p q : K[X]) : Nat :=
  2 * max (polySize p) (polySize q)
```

Prove positivity and:

```lean
theorem degree_lt_polySize [Semiring K] (p : K[X]) : p.degree < polySize p

theorem mul_degree_lt_multiplicationInputSize [Semiring K] (p q : K[X]) :
    (p * q).degree < multiplicationInputSize p q
```

Split zero and nonzero cases explicitly in the degree theorem.  Mathlib defines the zero polynomial's `natDegree` as zero, so this convention is positive without a decidable polynomial-equality branch and ensures zero and constant polynomials follow the same wrapper path.

- [ ] **Step 2: Define automatic exponent and capacity**

```lean
def complexFFTExponent (p q : ℂ[X]) : Nat :=
  fftExponent (multiplicationInputSize p q)

def complexFFTCapacity (p q : ℂ[X]) : Nat :=
  2 ^ complexFFTExponent p q
```

Prove product fit by composing `mul_degree_lt_multiplicationInputSize` with `fftCapacity_ge`.

- [ ] **Step 3: Define the principal complex root with the approved sign**

```lean
noncomputable def complexFFTRoot (p q : ℂ[X]) : ℂ :=
  Complex.exp
    (2 * Real.pi * Complex.I / (complexFFTCapacity p q : ℂ))
```

Prove:

```lean
theorem complexFFTRoot_isPrimitive (p q : ℂ[X]) :
    IsPrimitiveRoot (complexFFTRoot p q) (complexFFTCapacity p q) := by
  -- Apply `Complex.isPrimitiveRoot_exp`; discharge nonzero capacity by
  -- positivity of a power of two and normalize casts.
```

- [ ] **Step 4: Define the wrapper and prove unconditional correctness**

```lean
noncomputable def complexFFTMultiply (p q : ℂ[X]) : ℂ[X] :=
  fftMultiplyAt (k := complexFFTExponent p q) (complexFFTRoot p q) p q

theorem complexFFTMultiply_correct (p q : ℂ[X]) :
    complexFFTMultiply p q = p * q := by
  apply fftMultiplyAt_correct (complexFFTRoot_isPrimitive p q)
  exact complex_product_fits p q
```

No caller premise is allowed.  Add examples for zero times zero, zero times nonzero, constants, leading zero padding, and a nontrivial degree-two product.

- [ ] **Step 5: Verify and commit the complex wrapper**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.PolynomialMultiplication
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean \
  Tests/Chapter_30_PolynomialMultiplication_Interface.lean
git commit -m "feat(ch30): add arbitrary-input complex FFT multiplication"
```

### Task 5: Attach Exact Multiplication Work to Execution

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean`
- Test: `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`

- [ ] **Step 1: Define the numeric exact-capacity composition**

```lean
def radix2FFTMultiplyWork (k : Nat) : Nat :=
  3 * radix2FFTWork k + 2 * 2 ^ k
```

This is two forward FFTs, one inverse-root FFT, `2 ^ k` pointwise products, and `2 ^ k` inverse-scale products.

- [ ] **Step 2: Prove the execution counter equation**

Add:

```lean
theorem fftMultiplyExecAt_work_exact [Field K] {k : Nat}
    (omega : K) (p q : K[X]) :
    (fftMultiplyExecAt (k := k) omega p q).work =
      radix2FFTMultiplyWork k := by
  simp [fftMultiplyExecAt, scaleVectorExec, FFTMultiplicationExecution.work,
    radix2FFTMultiplyWork, recursiveFFTExec_addSubtractions,
    recursiveFFTExec_multiplications, pointwiseMulWork_exact, radix2FFTWork]
  omega
```

The theorem must unfold the actual pipeline counters; proving only a detached recurrence is insufficient.

- [ ] **Step 3: Add exact small-capacity cost examples**

Check `k = 0`, `k = 1`, and `k = 2`.  In at least one example, evaluate `fftMultiplyExecAt` itself and verify the value and work fields together.

### Task 6: Prove All-Input FFT Multiplication Work

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean`
- Test: `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`

- [ ] **Step 1: Define the fixed-capacity input cost universe**

For an advertised coefficient capacity `n` per operand, define:

```lean
def fftMultiplyExponent (n : Nat) : Nat :=
  fftExponent (2 * max 1 n)

def fftMultiplyWork (n : Nat) : Nat :=
  radix2FFTMultiplyWork (fftMultiplyExponent n)
```

Document that every polynomial with `degree < n` is charged at this declared capacity, even when leading coefficients vanish.  This prevents input-dependent sparsity from changing the denominator.

- [ ] **Step 2: Prove execution attachment for bounded inputs**

Add a wrapper execution using exponent `fftMultiplyExponent n` and prove:

```lean
theorem fftMultiplyExecution_work_eq (n : Nat) (p q : K[X]) :
    (fftMultiplyExecution n p q).work = fftMultiplyWork n := by
  exact fftMultiplyExecAt_work_exact _ _ _
```

Also prove correctness under `p.degree < n` and `q.degree < n`, deriving product fit from the doubled padded capacity.  Keep correctness and cost as separate public theorems over the same execution.

- [ ] **Step 3: Prove monotonicity and exact-power comparison**

Use monotonicity of `Nat.clog`, `fftCapacity`, and `radix2FFTMultiplyWork` to prove `Monotone fftMultiplyWork`.  At `n = 2 ^ k`, show the selected multiplication capacity is within one fixed factor of `2 ^ k`; derive constant-factor bounds against `(k + 1) * 2 ^ k`.

- [ ] **Step 4: Transfer to the all-input scale**

Reuse:

```lean
Chapter04.allInput_bigTheta_of_powerStep
Chapter04.criticalPowerLogScale_monotoneAbs
Chapter04.criticalPowerLogScale_powerStepBound
Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale
```

to prove:

```lean
theorem fftMultiplyWork_allInput_bigTheta :
    Chapter03.isBigTheta
      (fun n => (fftMultiplyWork n : ℝ))
      (Chapter04.realLogLogScale 2 2) := by
  -- Establish the exact-power `Theta` comparison, transfer to all inputs,
  -- then compose with the analytic real `n log n` scale.
```

The extra linear term `2 * capacity` must be bounded explicitly by the FFT term eventually; do not silently erase pointwise multiplication or inverse scaling.

- [ ] **Step 5: Verify and commit multiplication costs**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.PolynomialMultiplication
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/PolynomialMultiplication.lean \
  Tests/Chapter_30_PolynomialMultiplication_Interface.lean
git commit -m "feat(ch30): prove FFT multiplication work bounds"
```

### Task 7: Expose the Final Chapter Surface

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean`
- Modify: `CLRSLean/Chapter_30.lean`
- Modify: `CLRSLean.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Test: all five Chapter 30 tests

- [ ] **Step 1: Import the multiplication module from Section 30.2**

Add the import after RecursiveFFT Costs and update the Section 30.2 guide to name generic/complex multiplication correctness and execution-connected costs.

- [ ] **Step 2: Finalize the Chapter 30 guide**

State exactly:

- Section 30.1 is proved for coefficient/point-value representations and their represented operation costs;
- Section 30.2 is proved for generic DFT algebra, actual recursive radix-2 FFT, inverse, polynomial multiplication, and the declared exact/all-input arithmetic model;
- Section 30.3 remains deferred for bit-reversal, iterative FFT, stage invariants, and parallel circuit depth/size; and
- mutable arrays, RAM behavior, and floating-point error are outside the current exact-field model.

- [ ] **Step 3: Expose Chapter 30 from the root library**

Insert:

```lean
import CLRSLean.Chapter_30
```

between Chapter 27 and Chapter 32 in `CLRSLean.lean`.

- [ ] **Step 4: Register the final source and audit path**

Add `PolynomialMultiplication` to `literate.toml` and `docs/index.md`.  Add the dated audit path to `docs/index.md` after the audit is created in Task 9.

- [ ] **Step 5: Turn all focused interfaces GREEN**

Run:

```bash
lake env lean Tests/Chapter_30_Interface.lean
lake env lean Tests/Chapter_30_DFT_Interface.lean
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
```

Expected: all five exit 0.  Inspect closure axiom output and record it for the dated audit.

- [ ] **Step 6: Commit the final source wiring**

```bash
git add CLRSLean.lean CLRSLean/Chapter_30.lean \
  CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean \
  literate.toml docs/index.md \
  Tests/Chapter_30_PolynomialMultiplication_Interface.lean \
  Tests/Chapter_30_Milestone1_Closure.lean
git commit -m "feat(ch30): expose FFT multiplication milestone"
```

### Task 8: Update Proof Map and Status Truth

**Files:**
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-status-board.md` only if the active priority list changes
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`

- [ ] **Step 1: Add Chapter 30 to the proof map**

Create separate Section 30.1 and 30.2 entries.  List the representation, interpolation, DFT/inverse/convolution, recursive algorithm, multiplication, and cost theorem groups.  Record the exact FFT formula `2*k*2^k`, the multiplication composition `3*radix2FFTWork k + 2*2^k`, and both all-input `Theta(n log n)` theorems.  Name Section 30.3 as the only remaining core group.

- [ ] **Step 2: Compute the tracked theorem-group count mechanically**

Use the public interface tests and proof-map grouping policy:

```bash
rg -n '^#check ' \
  Tests/Chapter_30_Interface.lean \
  Tests/Chapter_30_DFT_Interface.lean \
  Tests/Chapter_30_RecursiveFFT_Interface.lean \
  Tests/Chapter_30_PolynomialMultiplication_Interface.lean
```

Collapse aliases, compatibility-only bridges, exact erasure equations, and multiple views of one result into one tracked group each.  Record the resulting reviewed integer as both `tracked_key_theorems` and `proved_tracked_theorems`; do not count helper lemmas merely to inflate progress.

- [ ] **Step 3: Update the Chapter 30 CSV row**

Change it to:

- `repo_status`: `partial`;
- `represented_sections`: `30.1;30.2`;
- `missing_core_groups`: `1`;
- `completion_read`: Sections 30.1-30.2 complete for the exact-field recursive FFT milestone;
- `proved_key_theorem_groups`: the reviewed public groups from Step 2;
- `remaining_core_groups`: Section 30.3 bit reversal, iterative FFT/stage invariant, and parallel FFT circuit depth/size;
- `evidence_source`: chapter aggregator, both section aggregators, all focused/closure tests, status page, proof map, and dated audit; and
- `notes`: exact field arithmetic and declared operation counts, excluding mutable/RAM/floating-point semantics.

- [ ] **Step 4: Update the reader-facing status page**

Add Chapter 30 under `Structured But Partial`, with Sections 30.1-30.2 and both all-input bounds summarized.  Rewrite `Not Represented On Main` from “Chapters 28--31” to name Chapters 28-29 and 31 explicitly.  Ensure no sentence implies all of Chapter 30 is complete.

- [ ] **Step 5: Update active priorities only if policy requires it**

If `docs/proof-status-board.md` still lists Chapter 30 as unrepresented or its active priority must advance, replace that entry with the explicit Section 30.3 next target.  If Chapter 30 is absent from the priority list, leave the file unchanged and record that decision in the audit.

- [ ] **Step 6: Regenerate derived status artifacts**

Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
```

Expected: all commands exit 0, the Chapter 30 row is `partial`, and generated totals agree with the CSV.

- [ ] **Step 7: Commit status truth**

```bash
git add docs/proof-map.md docs/clrs-proof-progress.csv \
  CLRSLean/Status.lean CLRSLean/Progress.lean README.md
git commit -m "docs(ch30): record FFT milestone status"
```

If `docs/proof-status-board.md` changed intentionally in Step 5, stage it with a separate `git add docs/proof-status-board.md` before the commit.  Before committing, use `git diff --name-only --cached` and do not stage unrelated files.

### Task 9: Create the Dated Milestone Audit

**Files:**
- Create: `docs/proof-audits/chapter-30-milestone-1-2026-08-05.md`
- Modify: `docs/index.md`

- [ ] **Step 1: Record scope and explicit exclusions**

The audit must state:

- the approved strong boundary for Sections 30.1-30.2;
- the generic characteristic-zero field core and exact complex wrapper;
- the fixed-vector/power-of-two representation;
- the actual recursive execution and successive-twiddle cost convention;
- the exact and all-input cost theorems; and
- Section 30.3, arrays/RAM, floating point, and exercises/problems as exclusions.

- [ ] **Step 2: Record theorem and axiom evidence**

Copy the final theorem types from the five interface tests and summarize the actual `#print axioms` output.  Do not write “axiom-free” if standard dependencies such as `propext`, `Classical.choice`, or `Quot.sound` appear; list the accepted dependencies accurately and state that `sorryAx` and project-defined axioms are absent.

- [ ] **Step 3: Record every verification command and result**

Include the focused tests, closure test, unfinished-proof scan, repository checks, site consistency, root library build, and literate site build with date and exit status.  Historical audit text must match the commands actually run in Task 10.

- [ ] **Step 4: Register and commit the audit**

Add the audit path to `docs/index.md`, then run:

```bash
uv run python scripts/check_repository.py
git diff --check
```

Expected: both exit 0.

```bash
git add docs/proof-audits/chapter-30-milestone-1-2026-08-05.md docs/index.md
git commit -m "docs(ch30): add FFT milestone audit"
```

### Task 10: Run the Full Milestone Closure Gate

**Files:**
- Verify: all Chapter 30 source, tests, and repository metadata

- [ ] **Step 1: Run all focused and closure tests from a clean command boundary**

```bash
lake env lean Tests/Chapter_30_Interface.lean
lake env lean Tests/Chapter_30_DFT_Interface.lean
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
```

Expected: every command exits 0.  Inspect, do not infer, the axiom output.

- [ ] **Step 2: Scan for unfinished proofs**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_30 -g '*.lean'
```

Expected: no matches.

- [ ] **Step 3: Run repository and documentation checks**

```bash
uv run python scripts/check_repository.py
uv run python scripts/check_site_consistency.py
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
git diff --check
```

Expected: every command exits 0.

- [ ] **Step 4: Build the root library**

Run:

```bash
lake build CLRSLean
```

Expected: exit 0 with Chapter 30 reachable through the root import.

- [ ] **Step 5: Build the literate site**

Run:

```bash
lake build :literateHtml
```

Expected: exit 0 and every registered Chapter 30 source renders.

- [ ] **Step 6: Reconcile the dated audit with fresh evidence**

If any command or axiom output differs from the audit, amend the audit and rerun repository/site checks.  The audit is evidence, not a prediction.

- [ ] **Step 7: Commit any evidence correction**

Only if Task 10 required an audit correction:

```bash
git add docs/proof-audits/chapter-30-milestone-1-2026-08-05.md
git commit -m "docs(ch30): reconcile milestone verification evidence"
```

### Task 11: Request Final Code Review and Close the Milestone

**Files:**
- Review: all files changed since the design commit

- [ ] **Step 1: Review the complete diff against the approved design**

Run:

```bash
git diff --stat 2d23276..HEAD
git diff --check 2d23276..HEAD
git log --oneline 2d23276..HEAD
```

Review every acceptance group in `docs/superpowers/specs/2026-08-05-chapter-30-milestone-1-design.md` against a concrete declaration and passing test.

- [ ] **Step 2: Apply the required review skill**

Use `superpowers:requesting-code-review` to perform an independent review of correctness, interface consistency, cost attachment, documentation truth, and closure evidence.  Resolve findings with focused tests, then rerun every affected closure command.

- [ ] **Step 3: Confirm the worktree handoff state**

Run:

```bash
git status --short
```

Expected: clean, unless the user has unrelated preserved changes.  Report any preserved changes explicitly.

## Plan 4 Acceptance Gate

- [ ] `fftMultiplyAt` is the value projection of the costed execution and equals `p*q` under the minimal fit premise.
- [ ] The arbitrary-input complex wrapper constructs its positive capacity and primitive root internally and is correct for zero, constant, and nontrivial inputs.
- [ ] Multiplication execution charges three recursive FFTs, pointwise products, and inverse scaling; exact work is connected to the execution object.
- [ ] The declared fixed-capacity all-input multiplication cost is `Theta(n log n)` through the Chapter 4 transfer infrastructure.
- [ ] Five Chapter 30 tests import only stable aggregators, pass, and closure output contains no `sorryAx` or project-defined axioms.
- [ ] Root library, repository checks, status generators, site consistency, and literate site build all pass.
- [ ] Proof map, CSV, generated dashboard, README, status page, chapter guide, and dated audit agree that 30.1-30.2 are proved and Chapter 30 is partial.
- [ ] Section 30.3 is the only named remaining main-text core group; mutable/RAM/floating-point refinements and exercises are clearly outside the milestone.
