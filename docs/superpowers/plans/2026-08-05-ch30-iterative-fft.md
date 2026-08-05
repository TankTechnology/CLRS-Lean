# Chapter 30 Iterative FFT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement flat ordered butterfly stages and prove that bit-reversal followed by all stages equals the existing recursive FFT and generic DFT.

**Architecture:** Each global stage is indexed by `Fin k` and recursively enumerates its independent contiguous blocks: a final stage on a block runs the proved `butterflyLayerExec`, while a nonfinal global stage acts independently on the two halves with squared root.  A prefix execution folds stages in increasing order; half-factorization of every nonfinal prefix yields the recursive FFT equation without expanding raw block arithmetic in the final proof.

**Tech Stack:** Lean 4.32.0-rc1, Section 30.2 butterfly/recursive FFT/DFT theorems, Milestone 2 bit reversal, `Fin`/functional extensionality, Lake, interface tests.

---

## Prerequisite

Complete `docs/superpowers/plans/2026-08-05-ch30-bit-reversal.md` first.  This
plan treats `bitReverseCopy`, its successor split, and its permutation semantics
as green interfaces.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Definitions.lean` for half extraction, stage executions, prefix executions, and the iterative FFT execution.
- Create `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Correctness.lean` for stage semantics, half-factorization, the recursive equation, and DFT correctness.
- Create `Tests/Chapter_30_IterativeFFT_Interface.lean` for the public iterative contract and exact small transforms.
- Modify `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean` to export the two modules.

### Task 1: Lock The Iterative Contract In RED

**Files:**
- Create: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Write the public checks**

Create:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check lowerHalf
#check upperHalf
#check FFTStageExecution
#check fftStageExec
#check fftStage
#check fftStage_final
#check fftStage_nonfinal
#check FFTStageSequenceExecution
#check runFFTStagePrefixExec
#check runAllFFTStagesExec
#check IterativeFFTExecution
#check iterativeRadix2FFTExec
#check iterativeRadix2FFT
#check runFFTStagePrefix_join
#check iterativeRadix2FFT_succ
#check iterativeRadix2FFT_eq_recursiveFFT
#check iterativeRadix2FFT_eq_dft

example (a : PowTwoVec ℚ 0) : iterativeRadix2FFT 1 a = a := by
  funext i
  fin_cases i
  rfl

end CLRS.Chapter30
```

- [ ] **Step 2: Verify RED**

```bash
lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean
```

Expected: nonzero exit on `Unknown constant CLRS.Chapter30.lowerHalf`.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_30_IterativeFFT_Interface.lean
git commit -m "test(ch30): specify iterative FFT interface"
```

### Task 2: Define Half Vectors And One Global Stage

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Definitions.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Define contiguous half extraction**

Import `BitReversal` and add:

```lean
def lowerHalf {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (lowerHalfIndex i)

def upperHalf {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (upperHalfIndex i)
```

Prove simp application lemmas plus:

```lean
@[simp] theorem lowerHalf_joinHalves (a b : PowTwoVec K k) :
    lowerHalf (joinHalves a b) = a := by funext i; simp [lowerHalf]

@[simp] theorem upperHalf_joinHalves (a b : PowTwoVec K k) :
    upperHalf (joinHalves a b) = b := by funext i; simp [upperHalf]

theorem joinHalves_lower_upper (a : PowTwoVec K (k + 1)) :
    joinHalves (lowerHalf a) (upperHalf a) = a := by
  funext i
  -- Split `i` through `powTwoSuccEquiv` and use `Fin.append` cases.
```

- [ ] **Step 2: Define the stage execution record**

```lean
structure FFTStageExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  addSubtractions : Nat
  multiplications : Nat
```

- [ ] **Step 3: Define a global stage by block recursion**

Use recursion on the transform exponent.  The stage index is always valid:

```lean
def fftStageExec [Ring K] :
    {k : Nat} → K → PowTwoVec K k → Fin k → FFTStageExecution K k
  | 0, _, _, s => Fin.elim0 s
  | k + 1, omega, a, s =>
      if hfinal : s.1 = k then
        let layer := butterflyLayerExec omega (lowerHalf a) (upperHalf a)
        ⟨layer.value, layer.addSubtractions, layer.multiplications⟩
      else
        let childStage : Fin k := ⟨s.1, by omega⟩
        let lowerRun := fftStageExec (omega ^ 2) (lowerHalf a) childStage
        let upperRun := fftStageExec (omega ^ 2) (upperHalf a) childStage
        ⟨joinHalves lowerRun.value upperRun.value,
          lowerRun.addSubtractions + upperRun.addSubtractions,
          lowerRun.multiplications + upperRun.multiplications⟩

def fftStage [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) (s : Fin k) : PowTwoVec K k :=
  (fftStageExec omega a s).value
```

This recursion enumerates every independent block of the one global stage.  It
does not recurse through the FFT problem after completing a stage.

- [ ] **Step 4: Expose final and nonfinal stage equations**

For the final index `Fin.last k`, prove:

```lean
theorem fftStage_final [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) :
    fftStage omega a (Fin.last k) =
      butterflyLayer omega (lowerHalf a) (upperHalf a) := by
  simp [fftStage, fftStageExec]
```

For `s : Fin k`, embedded with `Fin.castSucc`, prove:

```lean
theorem fftStage_nonfinal [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) (s : Fin k) :
    fftStage omega a s.castSucc =
      joinHalves
        (fftStage (omega ^ 2) (lowerHalf a) s)
        (fftStage (omega ^ 2) (upperHalf a) s) := by
  simp [fftStage, fftStageExec, Fin.castSucc]
```

Add matching equations for the execution counter fields; the costs plan will
consume them rather than unfold the recursive stage definition.

- [ ] **Step 5: Build the definitions module**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Definitions
```

Expected: exit 0.

### Task 3: Define Prefix And Complete Iterative Executions

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Definitions.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Define the sequence record**

```lean
structure FFTStageSequenceExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  addSubtractions : Nat
  multiplications : Nat
```

- [ ] **Step 2: Fold the first `m` stages in increasing order**

```lean
def runFFTStagePrefixExec [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (m : Nat) → m ≤ k → FFTStageSequenceExecution K k
  | 0, _ => ⟨a, 0, 0⟩
  | m + 1, hm =>
      let previous := runFFTStagePrefixExec omega a m (by omega)
      let current := fftStageExec omega previous.value ⟨m, hm⟩
      ⟨current.value,
        previous.addSubtractions + current.addSubtractions,
        previous.multiplications + current.multiplications⟩

def runAllFFTStagesExec [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : FFTStageSequenceExecution K k :=
  runFFTStagePrefixExec omega a k le_rfl
```

Add value projections `runFFTStagePrefix` and `runAllFFTStages`, plus zero and
successor unfolding lemmas whose right-hand sides use `fftStage`.

- [ ] **Step 3: Define the complete iterative execution**

```lean
structure IterativeFFTExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  bitReversalMoves : Nat
  addSubtractions : Nat
  multiplications : Nat

def iterativeRadix2FFTExec [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : IterativeFFTExecution K k :=
  let reversal := bitReverseExec a
  let stages := runAllFFTStagesExec omega reversal.value
  ⟨stages.value, reversal.moves,
    stages.addSubtractions, stages.multiplications⟩

def iterativeRadix2FFT [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  (iterativeRadix2FFTExec omega a).value
```

Prove the erasure equation by reflexivity and the exponent-zero identity by
function extensionality.

- [ ] **Step 4: Verify and commit definitions**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Definitions
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Definitions.lean
git commit -m "feat(ch30): implement iterative FFT stages"
```

Expected: build exit 0.

### Task 4: Prove The Prefix Half-Factorization Invariant

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Correctness.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Prove one nonfinal stage commutes with joining halves**

Import `Definitions` and `RecursiveFFT.Correctness`.  Use
`fftStage_nonfinal` and the half/join simp lemmas to prove:

```lean
theorem fftStage_join_castSucc [Ring K] {k : Nat} (omega : K)
    (lower upper : PowTwoVec K k) (s : Fin k) :
    fftStage omega (joinHalves lower upper) s.castSucc =
      joinHalves (fftStage (omega ^ 2) lower s)
        (fftStage (omega ^ 2) upper s) := by
  simpa using fftStage_nonfinal omega (joinHalves lower upper) s
```

- [ ] **Step 2: Prove the prefix invariant by induction on `m`**

```lean
theorem runFFTStagePrefix_join [Ring K] {k m : Nat} (hm : m ≤ k)
    (omega : K) (lower upper : PowTwoVec K k) :
    runFFTStagePrefix omega (joinHalves lower upper) m (hm.trans (Nat.le_succ k)) =
      joinHalves
        (runFFTStagePrefix (omega ^ 2) lower m hm)
        (runFFTStagePrefix (omega ^ 2) upper m hm) := by
  induction m with
  | zero => simp [runFFTStagePrefix]
  | succ m ih =>
      rw [runFFTStagePrefix_succ, runFFTStagePrefix_succ,
        runFFTStagePrefix_succ, ih]
      exact fftStage_join_castSucc _ _ _ ⟨m, by omega⟩
```

If proof arguments require proof irrelevance normalization, add a local
`Subsingleton.elim` rewrite lemma for the `m ≤ k` witnesses instead of exposing
casts in the public theorem.

- [ ] **Step 3: Specialize to all child stages**

Derive the stable invariant:

```lean
theorem runInitialFFTStages_join [Ring K] {k : Nat} (omega : K)
    (lower upper : PowTwoVec K k) :
    runFFTStagePrefix omega (joinHalves lower upper) k (Nat.le_succ k) =
      joinHalves
        (runAllFFTStages (omega ^ 2) lower)
        (runAllFFTStages (omega ^ 2) upper) := by
  simpa [runAllFFTStages] using
    runFFTStagePrefix_join (m := k) le_rfl omega lower upper
```

- [ ] **Step 4: Compile the invariant**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Correctness
```

Expected: exit 0 before adding final correctness.

### Task 5: Bridge Iterative FFT To Recursive FFT And DFT

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Correctness.lean`
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean`
- Test: `Tests/Chapter_30_IterativeFFT_Interface.lean`

- [ ] **Step 1: Prove the iterative successor equation**

Combine the recursive equation for `bitReverseCopy`,
`runInitialFFTStages_join`, and the final-stage theorem:

```lean
theorem iterativeRadix2FFT_succ [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) :
    iterativeRadix2FFT omega a =
      butterflyLayer omega
        (iterativeRadix2FFT (omega ^ 2) (evenCoeffs a))
        (iterativeRadix2FFT (omega ^ 2) (oddCoeffs a)) := by
  -- Unfold only the outer execution/value projections.
  -- Rewrite the bit-reversal successor split.
  -- Factor the first `k` stages and rewrite stage `k` as the final layer.
```

- [ ] **Step 2: Prove equality with the recursive execution**

```lean
theorem iterativeRadix2FFT_eq_recursiveFFT [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    iterativeRadix2FFT omega a = recursiveFFT omega a := by
  induction k generalizing omega a with
  | zero =>
      funext i
      fin_cases i
      rfl
  | succ k ih =>
      rw [iterativeRadix2FFT_succ]
      simp only [recursiveFFT, recursiveFFTExec]
      rw [ih, ih]
      -- Normalize `twiddleChildRoot` to `omega ^ 2` with the proved positive
      -- exponent theorem, then close by `rfl`/the butterfly erasure equation.
```

The proof may use the existing recursive successor lemma if exported; it must
not restate DFT algebra.

- [ ] **Step 3: Transfer correctness to the generic DFT**

```lean
theorem iterativeRadix2FFT_eq_dft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    iterativeRadix2FFT omega a = dft omega a := by
  rw [iterativeRadix2FFT_eq_recursiveFFT]
  exact recursiveFFT_eq_dft homega a
```

- [ ] **Step 4: Export and turn the interface GREEN**

Add imports for `Definitions` and `Correctness` to the Section 30.3 aggregator,
then run:

```bash
lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean
lake env lean Tests/Chapter_30_BitReversal_Interface.lean
rg -n "sorry|admit" \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT
```

Expected: both tests exit 0 and the scan has no matches.

- [ ] **Step 5: Commit correctness and exports**

```bash
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/IterativeFFT/Correctness.lean \
  Tests/Chapter_30_IterativeFFT_Interface.lean
git commit -m "feat(ch30): prove iterative FFT correctness"
```
