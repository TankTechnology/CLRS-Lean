# Chapter 30 Iterative FFT Costs Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove exact stage, complete iterative, and padded all-input costs from the fields of the actual Section 30.3 execution.

**Architecture:** Exact stage counts follow the same recursion that enumerates independent blocks; prefix counts sum the executions of the first `m` stages.  The complete execution combines the proved `2 ^ k` bit-reversal moves with `k` full stages, while padded all-input bounds reuse Milestone 1's capacity, monotonicity, and adjacent-power transfer infrastructure.

**Tech Stack:** Lean 4.32.0-rc1, Chapter 30 execution records, Chapter 3 asymptotic relations, Chapter 4 all-input transfer lemmas, Nat arithmetic, Lake, interface tests.

---

## Prerequisite

Complete `docs/superpowers/plans/2026-08-05-ch30-iterative-fft.md` first.  The
stage, prefix, and complete iterative execution records must be green before
any closed cost function is introduced.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean` for work projections, exact counters, asymptotics, and padded execution attachment.
- Modify `Tests/Chapter_30_IterativeFFT_Interface.lean` to add the cost contract and exact examples.
- Modify `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean` to export the costs module.

### Task 1: Extend The Interface With RED Cost Checks

**Files:**
- Modify: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Add the cost declarations to the test**

Append inside `CLRS.Chapter30`:

```lean
#check FFTStageExecution.work
#check IterativeFFTExecution.arithmeticWork
#check IterativeFFTExecution.totalWork
#check fftStageExec_addSubtractions
#check fftStageExec_multiplications
#check runFFTStagePrefixExec_addSubtractions
#check runFFTStagePrefixExec_multiplications
#check iterativeRadix2FFTExec_bitReversalMoves
#check iterativeRadix2FFTExec_addSubtractions
#check iterativeRadix2FFTExec_multiplications
#check iterativeRadix2FFTExec_arithmeticWork
#check iterativeRadix2FFTExec_totalWork
#check iterativeRadix2FFTTotalWork
#check iterativeRadix2FFTTotalWork_bigTheta
#check paddedIterativeFFTWork
#check iterativeRadix2FFTExec_zeroPad_totalWork
#check paddedIterativeFFTWork_allInput_bigTheta

example (omega : ℚ) (a : PowTwoVec ℚ 3) :
    (iterativeRadix2FFTExec omega a).arithmeticWork = 48 := by
  simpa using iterativeRadix2FFTExec_arithmeticWork omega a

example (omega : ℚ) (a : PowTwoVec ℚ 3) :
    (iterativeRadix2FFTExec omega a).totalWork = 56 := by
  simpa using iterativeRadix2FFTExec_totalWork omega a
```

- [ ] **Step 2: Verify the new checks are RED**

```bash
lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean
```

Expected: nonzero exit on `Unknown constant ...FFTStageExecution.work`, while
the earlier iterative correctness checks elaborate.

- [ ] **Step 3: Commit the RED extension**

```bash
git add Tests/Chapter_30_IterativeFFT_Interface.lean
git commit -m "test(ch30): specify iterative FFT costs"
```

### Task 2: Prove One Stage Has Exact Full-Length Arithmetic

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Define work projections**

Import `Correctness`, `RecursiveFFT.Costs`, and the Chapter 3/4 asymptotic
modules already used by `RecursiveFFT/Costs.lean`.  Add:

```lean
def FFTStageExecution.work (r : FFTStageExecution K k) : Nat :=
  r.addSubtractions + r.multiplications

def IterativeFFTExecution.arithmeticWork
    (r : IterativeFFTExecution K k) : Nat :=
  r.addSubtractions + r.multiplications

def IterativeFFTExecution.totalWork
    (r : IterativeFFTExecution K k) : Nat :=
  r.bitReversalMoves + r.arithmeticWork
```

- [ ] **Step 2: Prove exact stage additions/subtractions**

Induct on `k`.  The exponent-zero case eliminates `s : Fin 0`; at a successor,
split `s = Fin.last k` from `s.castSucc`.  Use the exported stage equations and
Milestone 1's `butterflyLayerExec_addSubtractions`:

```lean
@[simp] theorem fftStageExec_addSubtractions [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) (s : Fin k) :
    (fftStageExec omega a s).addSubtractions = 2 ^ k := by
  induction k generalizing omega a with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases h : s.1 = k
      · simp [fftStageExec, h, butterflyLayerExec_addSubtractions, pow_succ]
      · have hs : s.1 < k := by omega
        simp [fftStageExec, h, ih, pow_succ]
```

Normalize proof witnesses with proof irrelevance if the recursive `Fin` term
does not reduce definitionally.

- [ ] **Step 3: Prove exact stage multiplications**

Repeat the same structural proof using
`butterflyLayerExec_multiplications`:

```lean
@[simp] theorem fftStageExec_multiplications [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) (s : Fin k) :
    (fftStageExec omega a s).multiplications = 2 ^ k := by
  induction k generalizing omega a with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases h : s.1 = k
      · simp [fftStageExec, h, butterflyLayerExec_multiplications, pow_succ]
      · have hs : s.1 < k := by omega
        simp [fftStageExec, h, ih, pow_succ]
```

- [ ] **Step 4: Build the stage cost module**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Costs
```

Expected: exit 0.

### Task 3: Sum Prefix And Complete Execution Counters

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Prove exact prefix fields by induction on `m`**

```lean
@[simp] theorem runFFTStagePrefixExec_addSubtractions [Ring K]
    {k m : Nat} (omega : K) (a : PowTwoVec K k) (hm : m ≤ k) :
    (runFFTStagePrefixExec omega a m hm).addSubtractions = m * 2 ^ k := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [runFFTStagePrefixExec, ih, fftStageExec_addSubtractions,
        Nat.succ_mul]

@[simp] theorem runFFTStagePrefixExec_multiplications [Ring K]
    {k m : Nat} (omega : K) (a : PowTwoVec K k) (hm : m ≤ k) :
    (runFFTStagePrefixExec omega a m hm).multiplications = m * 2 ^ k := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [runFFTStagePrefixExec, ih, fftStageExec_multiplications,
        Nat.succ_mul]
```

- [ ] **Step 2: Prove each complete execution field**

Use the definitions and the exact bit-reversal theorem:

```lean
@[simp] theorem iterativeRadix2FFTExec_bitReversalMoves [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).bitReversalMoves = 2 ^ k := by
  simp [iterativeRadix2FFTExec]

@[simp] theorem iterativeRadix2FFTExec_addSubtractions [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).addSubtractions = k * 2 ^ k := by
  simp [iterativeRadix2FFTExec, runAllFFTStagesExec]

@[simp] theorem iterativeRadix2FFTExec_multiplications [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).multiplications = k * 2 ^ k := by
  simp [iterativeRadix2FFTExec, runAllFFTStagesExec]
```

- [ ] **Step 3: Prove arithmetic and total work**

```lean
theorem iterativeRadix2FFTExec_arithmeticWork [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).arithmeticWork = radix2FFTWork k := by
  simp [IterativeFFTExecution.arithmeticWork, radix2FFTWork]
  omega

def iterativeRadix2FFTTotalWork (k : Nat) : Nat :=
  2 ^ k + radix2FFTWork k

theorem iterativeRadix2FFTExec_totalWork [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).totalWork =
      iterativeRadix2FFTTotalWork k := by
  simp [IterativeFFTExecution.totalWork, iterativeRadix2FFTTotalWork,
    iterativeRadix2FFTExec_arithmeticWork]
```

- [ ] **Step 4: Verify exact examples and commit**

```bash
lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean \
  Tests/Chapter_30_IterativeFFT_Interface.lean
git commit -m "feat(ch30): prove exact iterative FFT work"
```

Expected: the `k = 3` examples reduce to arithmetic work 48 and total work 56.

### Task 4: Prove Exact-Power Asymptotics

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean`

- [ ] **Step 1: Reuse recursive arithmetic asymptotics**

Add a named theorem stating the arithmetic work is
`Theta(k * 2 ^ k)` by exact equality with `radix2FFTWork` and
`radix2FFTWork_bigTheta`.

- [ ] **Step 2: Bound the total exact-power work**

Prove the direct asymptotic relation:

```lean
theorem iterativeRadix2FFTTotalWork_bigTheta :
    Chapter03.isBigTheta
      (fun k => (iterativeRadix2FFTTotalWork k : ℝ))
      (fun k => (k : ℝ) * (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨3, by norm_num, 1, ?_⟩
    intro k hk
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simp [iterativeRadix2FFTTotalWork, radix2FFTWork]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (Nat.cast_nonneg _)]
    simp [iterativeRadix2FFTTotalWork, radix2FFTWork]
    positivity
```

Adjust only cast normalization required by the installed Mathlib; preserve
constants, threshold, and the explicit linear move term.

- [ ] **Step 3: Compile exact-power costs**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Costs
```

Expected: exit 0.

### Task 5: Attach Padded All-Input Work

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean`
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Define padded iterative work**

```lean
def paddedIterativeFFTWork (n : Nat) : Nat :=
  fftCapacity n + paddedFFTWork n
```

Prove monotonicity from `fftCapacity_monotone` and
`paddedFFTWork_monotone`.

- [ ] **Step 2: Prove attachment to zero-padded execution**

```lean
theorem iterativeRadix2FFTExec_zeroPad_totalWork [Ring K] {n : Nat}
    (omega : K) (a : CoeffVector K n) :
    (iterativeRadix2FFTExec (k := fftExponent n) omega
      (zeroPadToFFTCapacity a)).totalWork = paddedIterativeFFTWork n := by
  rw [iterativeRadix2FFTExec_totalWork]
  rfl
```

- [ ] **Step 3: Prove eventual comparison with padded recursive work**

For `2 ≤ n`, prove `1 ≤ fftExponent n`, hence:

```text
paddedFFTWork n <= paddedIterativeFFTWork n
paddedIterativeFFTWork n <= 2 * paddedFFTWork n
```

The second inequality uses
`fftCapacity n ≤ 2 * fftExponent n * fftCapacity n` at positive exponent.
Cast these pointwise bounds to real absolute values and package them as a
`Chapter03.isBigTheta` relation between the padded iterative and recursive work
functions.

- [ ] **Step 4: Transfer the existing all-input theorem**

```lean
theorem paddedIterativeFFTWork_allInput_bigTheta :
    Chapter03.isBigTheta
      (fun n : Nat => (paddedIterativeFFTWork n : ℝ))
      (Chapter04.realLogLogScale 2 2) := by
  exact Chapter03.isBigTheta_trans
    paddedIterativeFFTWork_isBigTheta_paddedFFTWork
    paddedFFTWork_allInput_bigTheta
```

- [ ] **Step 5: Export, verify, and commit**

Import `IterativeFFT.Costs` from the Section 30.3 aggregator, then run:

```bash
lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean
lake env lean Tests/Chapter_30_BitReversal_Interface.lean
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Costs
rg -n "sorry|admit" \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT
```

Expected: all Lean commands exit 0 and the scan has no matches.

```bash
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Costs.lean \
  Tests/Chapter_30_IterativeFFT_Interface.lean
git commit -m "feat(ch30): prove padded iterative FFT bounds"
```
