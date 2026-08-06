# Chapter 30 Recursive FFT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the actual radix-2 recursive FFT with even/odd splitting, successively generated twiddles, butterflies, inverse transform, exact execution counters, and exact-power plus padded all-input `Theta(n log n)` theorems.

**Architecture:** A single structurally recursive execution returns both a `PowTwoVec` value and arithmetic counters.  Recursive correctness follows the CLRS polynomial split and primitive-root reduction; the cost proof reads the same execution tree, then transfers the exact power-of-two formula to arbitrary positive sizes with the Chapter 4 adjacent-power infrastructure.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `Fin`/`Finset`/`List`/primitive-root APIs, CLRS Chapter 3 asymptotics, CLRS Chapter 4 all-input transfer lemmas, Lake, Verso, interface and axiom-closure tests.

---

## Prerequisite

Complete `docs/superpowers/plans/2026-08-05-ch30-dft-algebra.md` first.  This plan treats `dft`, `idft`, primitive-root squaring/inversion, and Fourier inversion as green upstream interfaces.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions.lean` for radix-2 index maps, successive twiddles, butterflies, execution records, recursive FFT, and recursive inverse FFT.
- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Correctness.lean` for split identities, twiddle semantics, FFT/DFT equality, and inverse round trips.
- Create `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs.lean` for exact counters and asymptotic theorems.
- Create `Tests/Chapter_30_RecursiveFFT_Interface.lean` for the public algorithm, exact small executions, correctness, inverse, and costs.
- Modify `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean`, `literate.toml`, and `docs/index.md` to expose and register the recursive FFT modules.
- Modify `docs/proof-map.md`, `docs/clrs-proof-progress.csv`, and `CLRSLean/Status.lean`, then regenerate `CLRSLean/Progress.lean` and the README table so the intermediate repository state records recursive FFT as proved while multiplication remains open.

### Task 1: Lock the Recursive Algorithm Contract in RED

**Files:**
- Create: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Add public checks for control structure, semantics, and cost**

Create the test importing only `CLRSLean.Chapter_30`:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check evenIndex
#check oddIndex
#check evenCoeffs
#check oddCoeffs
#check twiddlePowersAux
#check TwiddleExecution
#check twiddlePowersAuxExec
#check twiddlePowers
#check twiddlePowers_eq_pow
#check twiddleChildRoot
#check twiddleChildRoot_eq_square
#check butterflyLayer
#check ButterflyExecution
#check butterflyLayerExec
#check FFTExecution
#check FFTExecution.work
#check recursiveFFTExec
#check recursiveFFT
#check recursiveFFTExec_value
#check polynomial_evenOdd_split
#check recursiveFFT_eq_dft
#check recursiveIFFT
#check recursiveIFFT_eq_idft
#check recursiveIFFT_recursiveFFT
#check recursiveFFT_recursiveIFFT
#check recursiveFFTWork
#check recursiveFFTWork_exact
#check fftExponent
#check fftCapacity
#check paddedFFTWork
#check fftCapacity_ge
#check fftCapacity_lt_two_mul
#check paddedFFTWork_allInput_bigTheta

end CLRS.Chapter30
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
```

Expected: nonzero exit with `Unknown constant CLRS.Chapter30.evenIndex`.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_30_RecursiveFFT_Interface.lean
git commit -m "test(ch30): specify recursive FFT interface"
```

### Task 2: Implement Radix-2 Indexing and Even/Odd Splits

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Add power-of-two arithmetic helpers**

Import `S3_InversionAndConvolution` and prove named helpers for:

```lean
2 ^ (k + 1) = 2 ^ k + 2 ^ k
2 * i < 2 ^ (k + 1)            when i < 2 ^ k
2 * i + 1 < 2 ^ (k + 1)        when i < 2 ^ k
```

Use `pow_succ` and `omega`; keep these proofs out of every later index constructor.

- [ ] **Step 2: Define total even and odd index maps**

Add:

```lean
def evenIndex {k : Nat} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * i.1, by have := i.2; simp [pow_succ]; omega⟩

def oddIndex {k : Nat} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * i.1 + 1, by have := i.2; simp [pow_succ]; omega⟩

def evenCoeffs {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (evenIndex i)

def oddCoeffs {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (oddIndex i)
```

Prove simp lemmas for the `.val` fields and for applying `evenCoeffs`/`oddCoeffs`.

- [ ] **Step 3: Define and prove the half-vector join equivalence**

Construct:

```lean
def powTwoSuccEquiv (k : Nat) :
    Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k + 2 ^ k) :=
  finCongr (by rw [pow_succ]; omega)
```

Use the installed `finCongr`/`Fin.cast` API.  Then define a `joinHalves` wrapper around `Fin.append` and prove lower/upper application lemmas.  This isolates all casts from the butterfly and recursive correctness proofs.

- [ ] **Step 4: Compile the indexing foundation**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Definitions
```

Expected: exit 0 even though the remainder of the file is not yet present.

### Task 3: Implement Successive Twiddle Generation

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Define a current-value-carrying list execution**

Add:

```lean
structure TwiddleExecution (K : Type*) where
  value : List K
  next : K
  multiplications : Nat

def twiddlePowersAuxExec [Monoid K] (omega : K) : Nat → K → TwiddleExecution K
  | 0, current => ⟨[], current, 0⟩
  | n + 1, current =>
      let child := twiddlePowersAuxExec omega n (current * omega)
      ⟨current :: child.value, child.next, child.multiplications + 1⟩

def twiddlePowersAux [Monoid K] (omega : K) (n : Nat) (current : K) : List K :=
  (twiddlePowersAuxExec omega n current).value
```

Prove:

```lean
theorem twiddlePowersAuxExec_length [Monoid K]
    (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAuxExec omega n current).value.length = n := by
  induction n generalizing current <;> simp [twiddlePowersAuxExec, *]

theorem twiddlePowersAux_length [Monoid K] (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAux omega n current).length = n := by
  exact twiddlePowersAuxExec_length omega n current
```

- [ ] **Step 2: Expose the fixed-vector twiddle sequence from an execution**

Define a helper `twiddleVectorOfExecution` that converts a `TwiddleExecution` to `CoeffVector K n` under a proof that its value list has length `n`.  Define `twiddlePowers omega n` by applying that helper to `twiddlePowersAuxExec omega n 1`; do not rerun the generator to obtain the vector.  Then prove by induction on the accessed list position:

```lean
theorem twiddlePowers_eq_pow [Monoid K] (omega : K) (n : Nat) (i : Fin n) :
    twiddlePowers omega n i = omega ^ i.1 := by
  -- Generalize the current accumulator to `current * omega ^ i` first;
  -- specialize to `current = 1` only at the public theorem.
```

- [ ] **Step 3: Prove the generator execution's exact multiplication count**

Prove:

```lean
theorem twiddlePowersAuxExec_multiplications [Monoid K]
    (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAuxExec omega n current).multiplications = n := by
  induction n generalizing current <;> simp [twiddlePowersAuxExec, *]
```

The theorem includes the final update.  The butterfly execution will read this execution field rather than charge `omega ^ i` as a constant operation.

- [ ] **Step 4: Reuse generated powers as the recursive child root**

Define `twiddleChildRoot k omega run`, under the premise that `run` is the execution of `2 ^ k` twiddles from current value one:

- when `k = 0`, return `1`, because the children have length one and their DFT is root-independent;
- when `k = 1`, return `run.next`, which is `omega ^ 2` after the two charged updates; and
- when `2 ≤ k`, read the third trace value, also `omega ^ 2`.

Prove:

```lean
theorem twiddleChildRoot_eq_square [Monoid K] {k : Nat} (hk : 0 < k)
    (omega : K) :
    twiddleChildRoot k omega (twiddlePowersAuxExec omega (2 ^ k) 1) =
      omega ^ 2 := by
  -- Split `k = 1` from `2 ≤ k`; use the accumulator invariant in the first
  -- case and `twiddlePowers_eq_pow` at index two in the second.
```

This theorem lets the actual recursive execution reuse a multiplication already charged to twiddle generation.  It must not evaluate a fresh `omega ^ 2` beside the counters.

- [ ] **Step 5: Add an exact generator example**

For an exact ring value `omega`, prove that `twiddlePowers omega 4` is extensionally `[1, omega, omega^2, omega^3]` through `twiddlePowers_eq_pow`.  Do not replace the generator definition with fresh exponentiation to make this example trivial.

### Task 4: Implement Butterflies and the Canonical Recursive Execution

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Define the butterfly execution from generated twiddles**

Add:

```lean
structure ButterflyExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K (k + 1)
  addSubtractions : Nat
  multiplications : Nat

def butterflyLayerFromTwiddleExec [Ring K] {k : Nat} (omega : K)
    (twiddleRun : TwiddleExecution K)
    (hrun : twiddleRun = twiddlePowersAuxExec omega (2 ^ k) 1)
    (u v : PowTwoVec K k) : ButterflyExecution K k :=
  let w := twiddleVectorOfExecution twiddleRun
    (by simpa [hrun] using twiddlePowersAuxExec_length omega (2 ^ k) 1)
  ⟨joinHalves
      (fun j => u j + w j * v j)
      (fun j => u j - w j * v j),
    2 * 2 ^ k,
    2 ^ k + twiddleRun.multiplications⟩

def butterflyLayerExec [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) : ButterflyExecution K k :=
  let twiddleRun := twiddlePowersAuxExec omega (2 ^ k) 1
  butterflyLayerFromTwiddleExec omega twiddleRun rfl u v

def butterflyLayer [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) : PowTwoVec K (k + 1) :=
  (butterflyLayerExec omega u v).value
```

Prove that this `w` equals `twiddlePowers omega (2 ^ k)`, then prove lower and upper half simp theorems that rewrite values to the displayed formulas.  Also prove that the butterfly execution has exactly `2 * 2 ^ k` addition/subtractions and `2 * 2 ^ k` multiplications, using `twiddlePowersAuxExec_multiplications` for the second equation.  The public standalone layer evaluates one twiddle execution; the recursive kernel below passes an already evaluated run to `butterflyLayerFromTwiddleExec`.

- [ ] **Step 2: Define the canonical execution object**

```lean
structure FFTExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  addSubtractions : Nat
  multiplications : Nat

def FFTExecution.work (r : FFTExecution K k) : Nat :=
  r.addSubtractions + r.multiplications
```

The counters mean field addition/subtraction operations and field multiplication operations.  Root certification and proof construction are not included in the cost.

- [ ] **Step 3: Define one structural recursive FFT execution**

Use this recurrence:

```lean
def recursiveFFTExec [Ring K] : {k : Nat} → K → PowTwoVec K k → FFTExecution K k
  | 0, _, a => ⟨a, 0, 0⟩
  | k + 1, omega, a =>
      let twiddleRun := twiddlePowersAuxExec omega (2 ^ k) 1
      let childRoot := twiddleChildRoot k omega twiddleRun
      let evenRun := recursiveFFTExec childRoot (evenCoeffs a)
      let oddRun := recursiveFFTExec childRoot (oddCoeffs a)
      let layer := butterflyLayerFromTwiddleExec omega twiddleRun rfl
        evenRun.value oddRun.value
      ⟨layer.value,
        evenRun.addSubtractions + oddRun.addSubtractions + layer.addSubtractions,
        evenRun.multiplications + oddRun.multiplications + layer.multiplications⟩

def recursiveFFT [Ring K] {k : Nat} (omega : K) (a : PowTwoVec K k) :
    PowTwoVec K k := (recursiveFFTExec omega a).value
```

The butterfly's multiplication field is one `w * v` and one actual twiddle update per half-size index.  Its equal addition/subtraction field is the lower sum plus upper difference.  The recursive execution reads both fields from `layer`; it does not restate their closed forms.  For `k > 0`, `childRoot` is proved equal to `omega ^ 2`; for `k = 0`, it is `1` and the length-one children are root-independent.  Thus root squaring is not an uncharged extra field multiplication.

- [ ] **Step 4: Add the erasure theorem**

```lean
theorem recursiveFFTExec_value [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (recursiveFFTExec omega a).value = recursiveFFT omega a := rfl
```

This apparently small theorem is the public link used by closure checks; retain it even though `recursiveFFT` is the projection.

- [ ] **Step 5: Define recursive inverse FFT**

```lean
def recursiveIFFT [Field K] {k : Nat} (omega : K) (a : PowTwoVec K k) :
    PowTwoVec K k :=
  fun i => ((2 ^ k : Nat) : K)⁻¹ * recursiveFFT omega⁻¹ a i
```

Keep inverse scaling outside the recursive kernel, matching `idft`.  Multiplication-pipeline costs will add these `2 ^ k` scale multiplications explicitly.

- [ ] **Step 6: Verify and commit the complete definitions**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Definitions
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Definitions.lean
git commit -m "feat(ch30): implement executable recursive FFT"
```

### Task 5: Prove the Polynomial Split and Butterfly Semantics

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Correctness.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Prove coefficient partition and the polynomial split**

Import Definitions and prove that every index below `2 ^ (k + 1)` is uniquely even or odd.  Then state:

```lean
theorem polynomial_evenOdd_split [CommRing K] {k : Nat}
    (a : PowTwoVec K (k + 1)) :
    vectorToPolynomial a =
      (vectorToPolynomial (evenCoeffs a)).comp (Polynomial.X ^ 2) +
      Polynomial.X * (vectorToPolynomial (oddCoeffs a)).comp (Polynomial.X ^ 2) := by
  ext i
  -- Split `i` by parity and use the coefficient bridge for the corresponding
  -- half vector.  Handle indices outside capacity with the support theorem.
```

If a direct coefficient proof is unwieldy, first prove the finite-sum partition and then rewrite the two sums.  Do not derive this identity from DFT correctness, because it is the induction invariant used to prove correctness.

- [ ] **Step 2: Derive the lower and upper DFT split identities**

For `homega : IsPrimitiveRoot omega (2 ^ (k + 1))`, prove pointwise:

```text
dft omega a j
  = dft (omega^2) (evenCoeffs a) j
    + omega^j * dft (omega^2) (oddCoeffs a) j

dft omega a (j + 2^k)
  = dft (omega^2) (evenCoeffs a) j
    - omega^j * dft (omega^2) (oddCoeffs a) j
```

Use `primitiveRoot_half_pow_eq_neg_one` for the upper identity and `twiddlePowers_eq_pow` to align the implementation's successive twiddle vector with the specification.

- [ ] **Step 3: Prove butterfly output agreement**

Package the previous pointwise equations as a vector theorem saying that `butterflyLayer omega (dft (omega^2) even) (dft (omega^2) odd) = dft omega a`.  Use `joinHalves` application lemmas to avoid cast arithmetic in the final induction.

### Task 6: Prove Recursive FFT and Inverse Correctness

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Correctness.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Prove the headline FFT theorem by structural induction**

Add:

```lean
theorem recursiveFFT_eq_dft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveFFT omega a = dft omega a := by
  induction k with
  | zero =>
      funext i
      fin_cases i
      simp [recursiveFFT, recursiveFFTExec, dft]
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        -- Both recursive children have length one; normalize
        -- `twiddleChildRoot` to `1` and discharge the base calls directly.
      · have hchildRoot :
            twiddleChildRoot k omega
              (twiddlePowersAuxExec omega (2 ^ k) 1) = omega ^ 2 :=
          twiddleChildRoot_eq_square (Nat.pos_of_ne_zero hk) omega
        have hsquare : IsPrimitiveRoot (omega ^ 2) (2 ^ k) := by
          apply primitiveRoot_square (by positivity)
          simpa [pow_succ, two_mul] using homega
        -- Rewrite the actual child root with `hchildRoot`, apply both
        -- induction hypotheses under `hsquare`, then use the butterfly theorem.
      simp only [recursiveFFT, recursiveFFTExec]
```

The actual induction syntax may require generalizing `omega` and `a`.  The theorem may not accept recursive-correctness certificates as premises.

- [ ] **Step 2: Prove inverse agreement and both round trips**

Add:

```lean
theorem recursiveIFFT_eq_idft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveIFFT omega a = idft omega a := by
  funext i
  simp [recursiveIFFT, idft, recursiveFFT_eq_dft (primitiveRoot_inv homega)]

theorem recursiveIFFT_recursiveFFT [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveIFFT omega (recursiveFFT omega a) = a := by
  rw [recursiveIFFT_eq_idft homega, recursiveFFT_eq_dft homega,
    idft_dft (by positivity) homega]

theorem recursiveFFT_recursiveIFFT [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveFFT omega (recursiveIFFT omega a) = a := by
  rw [recursiveFFT_eq_dft homega, recursiveIFFT_eq_idft homega,
    dft_idft (by positivity) homega]
```

- [ ] **Step 3: Add size-one, size-two, and size-four execution examples**

Use exact inputs and proved roots.  At least one example must unfold `recursiveFFTExec` far enough to verify the actual output and counters, and at least one must use the abstract correctness theorem rather than computation.

- [ ] **Step 4: Verify and inspect axioms**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Correctness
```

Add temporary `#print axioms` commands to the focused test for `polynomial_evenOdd_split`, `recursiveFFT_eq_dft`, `recursiveIFFT_eq_idft`, and both round trips; run the test directly.

Expected: no `sorryAx` and no project-defined axioms.

- [ ] **Step 5: Commit recursive correctness**

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Correctness.lean \
  Tests/Chapter_30_RecursiveFFT_Interface.lean
git commit -m "feat(ch30): prove recursive FFT correctness"
```

### Task 7: Prove Exact Execution Counts

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Define the analyzed work as the execution's work**

Import Correctness and define:

```lean
def recursiveFFTWork [Ring K] {k : Nat} (omega : K) (a : PowTwoVec K k) : Nat :=
  (recursiveFFTExec omega a).work
```

Then prove the counter recurrences by unfolding `recursiveFFTExec` once and applying the butterfly execution count theorems.  At level `k + 1`, each counter receives `2 * 2 ^ k`; combined current-level work is `4 * 2 ^ k = 2 * 2 ^ (k + 1)`.

- [ ] **Step 2: Prove exact counter closed forms**

Prove, by induction on `k`:

```lean
theorem recursiveFFTExec_addSubtractions [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (recursiveFFTExec omega a).addSubtractions = k * 2 ^ k := by
  induction k generalizing omega a <;> simp [recursiveFFTExec, *, pow_succ]
  omega

theorem recursiveFFTExec_multiplications [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (recursiveFFTExec omega a).multiplications = k * 2 ^ k := by
  induction k generalizing omega a <;> simp [recursiveFFTExec, *, pow_succ]
  omega

theorem recursiveFFTWork_exact [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    recursiveFFTWork omega a = 2 * k * 2 ^ k := by
  rw [recursiveFFTWork, FFTExecution.work,
    recursiveFFTExec_addSubtractions, recursiveFFTExec_multiplications]
  ring
```

Use `omega` for natural-number normalization if `ring` does not close the final identity.

- [ ] **Step 3: State the exact-power asymptotic theorem**

Define the numeric closed form independently of `K` only after proving the execution equation:

```lean
def radix2FFTWork (k : Nat) : Nat := 2 * k * 2 ^ k
```

Prove `recursiveFFTWork_eq_radix2FFTWork`, then prove the sequence-level `Theta` result against `fun k => (k : ℝ) * 2 ^ k`.  This is the exact-power theorem, not the all-input claim.

- [ ] **Step 4: Verify and commit exact costs**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Costs
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs.lean
git commit -m "feat(ch30): prove exact recursive FFT work"
```

### Task 8: Transfer FFT Work to Arbitrary Positive Sizes

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs.lean`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Define padding exponent, capacity, and work**

Import `CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input` and Mathlib's `Nat.clog` module.  Define total conventions:

```lean
def fftExponent (n : Nat) : Nat := Nat.clog 2 (max 1 n)

def fftCapacity (n : Nat) : Nat := 2 ^ fftExponent n

def paddedFFTWork (n : Nat) : Nat := radix2FFTWork (fftExponent n)
```

`max 1 n` keeps the transform capacity nonempty.  Asymptotic statements may ignore the finite `n = 0` difference, but definitions and examples must still be total there.

- [ ] **Step 2: Prove padding bounds**

Use `Nat.le_pow_clog`, `Nat.clog_pow`, and `Nat.pow_pred_clog_lt_self` to prove:

```lean
theorem fftCapacity_ge (n : Nat) : n ≤ fftCapacity n := by
  -- Reduce to `max 1 n` and use `Nat.le_pow_clog` for base 2.

theorem fftCapacity_lt_two_mul {n : Nat} (hn : 1 < n) :
    fftCapacity n < 2 * n := by
  -- The previous power is below `n`; multiply by two and normalize the
  -- successor exponent.  Handle `fftExponent n = 0` by contradiction.
```

Also prove `fftCapacity_isPowerOfTwo`, positivity, and monotonicity of `fftExponent`, `fftCapacity`, and `paddedFFTWork`.

- [ ] **Step 3: Prove the exact-power identity for padded work**

For every `k`, prove:

```lean
theorem paddedFFTWork_pow (k : Nat) :
    paddedFFTWork (2 ^ k) = 2 * k * 2 ^ k := by
  simp [paddedFFTWork, radix2FFTWork, fftExponent, Nat.clog_pow]
```

Handle the exact spelling and positivity premises of `Nat.clog_pow` from the installed Mathlib version.

- [ ] **Step 4: Apply the Chapter 4 all-input bridge**

First prove the exact-power sequences
`k ↦ (paddedFFTWork (2 ^ k) : ℝ)` and
`k ↦ Chapter04.criticalPowerLogScale 2 2 (2 ^ k)`
are `Theta`.  The former is `2*k*2^k`; the latter is `(k+1)*2^k`, so prove the two constant-factor inequalities explicitly for all sufficiently large `k`.

Then apply:

```lean
Chapter04.allInput_bigTheta_of_powerStep
Chapter04.criticalPowerLogScale_monotoneAbs
Chapter04.criticalPowerLogScale_powerStepBound
Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale
```

to obtain:

```lean
theorem paddedFFTWork_allInput_bigTheta :
    Chapter03.isBigTheta
      (fun n => (paddedFFTWork n : ℝ))
      (Chapter04.realLogLogScale 2 2) := by
  -- First transfer to `criticalPowerLogScale 2 2`, then compose its analytic
  -- equivalence with the real `n log n` scale.
```

Use the repository's transitivity lemma for `isBigTheta`; do not substitute an informal comment for the final analytic bridge.

- [ ] **Step 5: Connect arbitrary-size padding back to execution**

Define a zero-padding function from `CoeffVector K n` to `CoeffVector K (fftCapacity n)` and prove that every original coefficient is preserved and every added slot is zero.  Then add an equation saying the `recursiveFFTExec` work at exponent `fftExponent n` equals `paddedFFTWork n`.  This is the execution attachment required by the milestone.

- [ ] **Step 6: Verify all cost theorems**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Costs
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
```

The test remains RED only until the aggregator imports Costs in Task 9.

- [ ] **Step 7: Commit all-input FFT costs**

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT/Costs.lean \
  Tests/Chapter_30_RecursiveFFT_Interface.lean
git commit -m "feat(ch30): prove padded FFT all-input bound"
```

### Task 9: Expose and Verify the Recursive FFT Surface

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Status.lean`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`
- Test: `Tests/Chapter_30_RecursiveFFT_Interface.lean`

- [ ] **Step 1: Extend the Section 30.2 aggregator**

Import Definitions, Correctness, and Costs after S3.  Update the reader guide to name the actual even/odd recursive execution, inverse, exact count, and padded all-input theorem.  Continue to state that FFT polynomial multiplication is added by the final plan and Section 30.3 remains deferred.

- [ ] **Step 2: Register all recursive FFT modules**

Add the three modules to `literate.toml` in dependency order and to `docs/index.md`.

- [ ] **Step 3: Update the truthful intermediate recursive-FFT status**

Extend `docs/proof-map.md` with recursive correctness, inverse, execution refinement, exact counters, and padded all-input work.  Keep the CSV represented sections at `30.1;30.2` and status `partial`; update reviewed theorem-group counts and record two remaining core groups: FFT polynomial multiplication and Section 30.3.  Update the Chapter 30 status paragraph and regenerate:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py
```

Expected: both exit 0, with multiplication still explicitly open.

- [ ] **Step 4: Turn the recursive interface GREEN**

Run:

```bash
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
lake env lean Tests/Chapter_30_DFT_Interface.lean
lake env lean Tests/Chapter_30_Interface.lean
lake build +CLRSLean.Chapter_30
uv run python scripts/check_repository.py
git diff --check
```

Expected: every command exits 0.

- [ ] **Step 5: Scan implementation and closure axioms**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT/RecursiveFFT \
  Tests/Chapter_30_RecursiveFFT_Interface.lean
```

Expected: no matches.  Inspect the focused test's `#print axioms` output for recursive correctness, inverse correctness, execution refinement, exact work, and all-input `Theta`; reject `sorryAx` and project-defined axioms.

- [ ] **Step 6: Commit the recursive FFT assembly**

```bash
git add CLRSLean/Chapter_30/Section_30_2_DFT_And_FFT.lean \
  literate.toml docs/index.md docs/proof-map.md \
  docs/clrs-proof-progress.csv CLRSLean/Status.lean \
  CLRSLean/Progress.lean README.md
git commit -m "feat(ch30): expose recursive FFT and costs"
```

## Plan 3 Acceptance Gate

- [ ] `recursiveFFTExec` visibly recurses on even/odd vectors with `omega ^ 2` and combines them through one butterfly layer.
- [ ] Twiddle values are generated successively; the exact multiplication counter charges every generator update.
- [ ] The recursive child root is recovered from the charged twiddle execution (except root-independent size-one children), so `omega ^ 2` is not an uncounted operation.
- [ ] Recursive counters are sums of child and butterfly execution fields, not a detached recurrence embedded beside the value algorithm.
- [ ] `recursiveFFT_eq_dft` follows structural induction and has no recursive-correctness certificate premise.
- [ ] Recursive inverse agrees with `idft` and is both a left and right inverse.
- [ ] Each counter is exactly `k * 2 ^ k`, so total execution work is exactly `2 * k * 2 ^ k`.
- [ ] Padding supplies `n ≤ fftCapacity n`, `fftCapacity n < 2*n` for `1<n`, and an execution-connected all-input `Theta(n log n)` theorem.
- [ ] Exact size-one, size-two, and size-four tests pass without approximate arithmetic.
- [ ] All recursive FFT modules and focused tests contain no unfinished proofs or project-defined axioms.
