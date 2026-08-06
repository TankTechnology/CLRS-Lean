# Chapter 30 Parallel FFT And Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the explicit layered FFT network, prove its evaluation and exact circuit size/depth, then close all Chapter 30 source, test, audit, progress, repository, and source navigation configuration gates.

**Architecture:** A typed network contains one canonical layer for every `Fin k` stage and one typed butterfly position for every block/within-half pair.  Evaluation folds the same verified stage semantics after bit-reversal wiring; logical circuit counts treat twiddle powers as fixed constants and remain separate from the execution model that charges twiddle generation.  Status changes occur only after all nine Chapter 30 tests and both full builds pass.

**Tech Stack:** Lean 4.32.0-rc1, Section 30.3 iterative execution/costs, Chapter 27 work/span terminology, Mathlib finite-cardinality arithmetic, Lake, Verso, repository progress generators, interface and axiom-closure tests.

---

## Prerequisite

Complete `docs/superpowers/plans/2026-08-05-ch30-iterative-costs.md` first.  The
parallel network reuses the proved `fftStage`, ordered prefix execution,
bit-reversal copy, iterative correctness, and exact execution counters.

## File Map

- Create `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean` for typed layers, network evaluation, and circuit counts.
- Create `Tests/Chapter_30_ParallelFFT_Interface.lean` for network semantics and size/depth.
- Create `Tests/Chapter_30_Milestone2_Closure.lean` for Chapter 30 headline checks and axiom output.
- Modify the Chapter 30 aggregators, `CLRSLean.lean`, `literate.toml`, and `docs/index.md` for the final source surface.
- Modify `docs/proof-map.md`, `docs/clrs-proof-progress.csv`, and `CLRSLean/Status.lean`; regenerate `CLRSLean/Progress.lean` and `README.md`.
- Create `docs/proof-audits/chapter-30-milestone-2-2026-08-05.md` with fresh evidence.

### Task 1: Lock Parallel And Closure Contracts In RED

**Files:**
- Create: `Tests/Chapter_30_ParallelFFT_Interface.lean`
- Create: `Tests/Chapter_30_Milestone2_Closure.lean`

- [ ] **Step 1: Write the parallel network interface**

Create:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check FFTButterflyPosition
#check FFTLayer
#check fftLayer
#check FFTLayer.root
#check FFTLayer.twiddle
#check FFTNetwork
#check fftNetwork
#check FFTNetwork.evalLayers
#check FFTNetwork.eval
#check fftNetwork_evalLayers
#check fftNetwork_eval
#check FFTLayer.butterflyCount
#check fftLayer_butterflyCount
#check FFTNetwork.butterflyCount
#check fftNetwork_butterflyCount
#check FFTNetwork.butterflyDepth
#check fftNetwork_butterflyDepth
#check FFTNetwork.primitiveGateCount
#check fftNetwork_primitiveGateCount
#check FFTNetwork.primitiveDepth
#check fftNetwork_primitiveDepth

example (omega : ℚ) : (fftNetwork (k := 3) omega).butterflyCount = 12 := by
  simpa using fftNetwork_butterflyCount (k := 3) omega

example (omega : ℚ) : (fftNetwork (k := 3) omega).butterflyDepth = 3 := by
  simpa using fftNetwork_butterflyDepth (k := 3) omega

example (omega : ℚ) : (fftNetwork (k := 3) omega).primitiveGateCount = 36 := by
  simpa using fftNetwork_primitiveGateCount (k := 3) omega

example (omega : ℚ) : (fftNetwork (k := 3) omega).primitiveDepth = 6 := by
  simpa using fftNetwork_primitiveDepth (k := 3) omega

end CLRS.Chapter30
```

- [ ] **Step 2: Write the final closure test**

Create `Tests/Chapter_30_Milestone2_Closure.lean`, importing only
`CLRSLean.Chapter_30`.  Add `#check` for:

```lean
bitReverseEquiv_testBit
bitReverseEquiv_involutive
bitReverseCopy_apply
bitReverseCopy_involutive
bitReverseExec_moves
runFFTStagePrefix_join
iterativeRadix2FFT_succ
iterativeRadix2FFT_eq_recursiveFFT
iterativeRadix2FFT_eq_dft
iterativeRadix2FFTExec_arithmeticWork
iterativeRadix2FFTExec_totalWork
paddedIterativeFFTWork_allInput_bigTheta
fftNetwork_eval
fftNetwork_butterflyCount
fftNetwork_butterflyDepth
fftNetwork_primitiveGateCount
fftNetwork_primitiveDepth
```

Add `#print axioms` for:

```lean
bitReverseEquiv_testBit
bitReverseCopy_involutive
iterativeRadix2FFT_eq_recursiveFFT
iterativeRadix2FFT_eq_dft
iterativeRadix2FFTExec_totalWork
paddedIterativeFFTWork_allInput_bigTheta
fftNetwork_eval
fftNetwork_butterflyCount
fftNetwork_primitiveDepth
```

- [ ] **Step 3: Verify both tests are RED**

```bash
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
lake env lean Tests/Chapter_30_Milestone2_Closure.lean
```

Expected: the parallel test fails on missing `FFTButterflyPosition`; closure
fails on the same missing parallel boundary while earlier Milestone 2 checks
elaborate.

- [ ] **Step 4: Commit RED contracts**

```bash
git add Tests/Chapter_30_ParallelFFT_Interface.lean \
  Tests/Chapter_30_Milestone2_Closure.lean
git commit -m "test(ch30): specify parallel FFT closure"
```

### Task 2: Define Typed Layers And Canonical Network Evaluation

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean`
- Test: `Tests/Chapter_30_ParallelFFT_Interface.lean`

- [ ] **Step 1: Define butterfly positions and layers**

Import `IterativeFFT.Costs`.  Add:

```lean
abbrev FFTButterflyPosition (k : Nat) (s : Fin k) :=
  Fin (2 ^ (k - s.1 - 1)) × Fin (2 ^ s.1)

structure FFTLayer (K : Type*) (k : Nat) where
  omega : K
  stage : Fin k

def fftLayer (omega : K) {k : Nat} (s : Fin k) : FFTLayer K k :=
  ⟨omega, s⟩

def FFTLayer.root [Monoid K] (layer : FFTLayer K k) : K :=
  layer.omega ^ (2 ^ (k - layer.stage.1 - 1))

def FFTLayer.twiddle [Monoid K] (layer : FFTLayer K k)
    (position : FFTButterflyPosition k layer.stage) : K :=
  layer.root ^ position.2.1
```

The position's first coordinate is the contiguous block; the second is the
within-half offset.  The layer root matches the CLRS stage root.

- [ ] **Step 2: Define an explicit network and layer fold**

```lean
structure FFTNetwork (K : Type*) (k : Nat) where
  layers : Fin k → FFTLayer K k

def fftNetwork {K : Type*} {k : Nat} (omega : K) : FFTNetwork K k :=
  ⟨fun s => fftLayer omega s⟩
```

Define `FFTNetwork.evalPrefix` by recursion on `m ≤ k`, applying
`fftStage (network.layers ⟨m, hm⟩).omega` at that layer's stage.  Define:

```lean
def FFTNetwork.evalLayers [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  network.evalPrefix a k le_rfl

def FFTNetwork.eval [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  network.evalLayers (bitReverseCopy a)
```

- [ ] **Step 3: Prove canonical evaluation equals the iterative algorithm**

Induct on prefix length to show the canonical network prefix equals
`runFFTStagePrefix`; then derive:

```lean
theorem fftNetwork_evalLayers [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (fftNetwork omega).evalLayers a = runAllFFTStages omega a := by
  simpa [FFTNetwork.evalLayers, runAllFFTStages] using
    fftNetwork_evalPrefix (k := k) omega a k le_rfl

theorem fftNetwork_eval [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (fftNetwork omega).eval a = iterativeRadix2FFT omega a := by
  simp [FFTNetwork.eval, iterativeRadix2FFT, iterativeRadix2FFTExec,
    fftNetwork_evalLayers]
```

- [ ] **Step 4: Build and commit network semantics**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.ParallelFFT
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean
git commit -m "feat(ch30): define layered FFT network"
```

Expected: build exit 0.

### Task 3: Prove Exact Butterfly And Gate Counts

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean`
- Test: `Tests/Chapter_30_ParallelFFT_Interface.lean`

- [ ] **Step 1: Define layer and network butterfly counts**

```lean
def FFTLayer.butterflyCount (layer : FFTLayer K k) : Nat :=
  Fintype.card (FFTButterflyPosition k layer.stage)

def FFTNetwork.butterflyCount (network : FFTNetwork K k) : Nat :=
  ∑ s : Fin k, (network.layers s).butterflyCount
```

- [ ] **Step 2: Prove every canonical layer has `2 ^ (k - 1)` butterflies**

Use `Fintype.card_prod`, `Fintype.card_fin`, `pow_add`, and
`layer.stage.2` to normalize:

```lean
theorem fftLayer_butterflyCount {K : Type*} {k : Nat}
    (omega : K) (s : Fin k) :
    (fftLayer omega s).butterflyCount = 2 ^ (k - 1) := by
  simp [FFTLayer.butterflyCount, FFTButterflyPosition]
  rw [← pow_add]
  congr 1
  omega
```

- [ ] **Step 3: Sum the canonical network**

```lean
theorem fftNetwork_butterflyCount {K : Type*} {k : Nat} (omega : K) :
    (fftNetwork omega : FFTNetwork K k).butterflyCount =
      k * 2 ^ (k - 1) := by
  simp [FFTNetwork.butterflyCount, fftNetwork, fftLayer_butterflyCount]
```

- [ ] **Step 4: Define and prove logical depths and primitive gates**

```lean
def FFTNetwork.butterflyDepth (_network : FFTNetwork K k) : Nat := k

def FFTNetwork.primitiveGateCount (network : FFTNetwork K k) : Nat :=
  3 * network.butterflyCount

def FFTNetwork.primitiveDepth (network : FFTNetwork K k) : Nat :=
  2 * network.butterflyDepth
```

Prove canonical closed forms:

```lean
@[simp] theorem fftNetwork_butterflyDepth (omega : K) :
    (fftNetwork (k := k) omega).butterflyDepth = k := rfl

theorem fftNetwork_primitiveGateCount (omega : K) :
    (fftNetwork (k := k) omega).primitiveGateCount =
      3 * k * 2 ^ (k - 1) := by
  simp [FFTNetwork.primitiveGateCount, fftNetwork_butterflyCount,
    Nat.mul_assoc]

@[simp] theorem fftNetwork_primitiveDepth (omega : K) :
    (fftNetwork (k := k) omega).primitiveDepth = 2 * k := rfl
```

Document beside these definitions that twiddle constants and bit-reversal
wiring are not arithmetic gates, while the execution cost separately charges
successive twiddle updates.

- [ ] **Step 5: Turn parallel tests GREEN and commit**

Import `ParallelFFT` from the Section 30.3 aggregator, then run:

```bash
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
lake env lean Tests/Chapter_30_Milestone2_Closure.lean
rg -n "sorry|admit" \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean
```

Expected: both tests exit 0 and the scan has no matches.  Inspect the closure
axiom output and retain it for the dated audit.

```bash
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean \
  Tests/Chapter_30_ParallelFFT_Interface.lean \
  Tests/Chapter_30_Milestone2_Closure.lean
git commit -m "feat(ch30): prove FFT circuit size and depth"
```

### Task 4: Finalize The Reader And Build Surface

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean`
- Modify: `CLRSLean/Chapter_30.lean`
- Modify: `CLRSLean.lean` only if the root import is not already present
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Finalize the Section 30.3 guide**

State that the section proves functional bit reversal, ordered iterative
stages, their factorization invariant, equality with recursive FFT/DFT, exact
execution costs, padded all-input `Theta(n log n)`, and the explicit layered
network.  State separately that arrays/RAM/cache/floating point and scheduler
overheads are excluded.

- [ ] **Step 2: Finalize the Chapter 30 guide**

Remove the old Section 30.3 deferred-gap wording.  Mark Sections 30.1--30.3 as
proved within exact generic arithmetic and list the exercise/problem and
machine-model exclusions.

- [ ] **Step 3: Register every new source for the literate site**

Add the Section 30.3 aggregator and its five focused source files to
`literate.toml` in dependency order.  Add reader links to `docs/index.md`.
Keep `CLRSLean.lean`'s existing Chapter 30 import in numerical chapter order.

- [ ] **Step 4: Run all nine Chapter 30 tests**

```bash
lake env lean Tests/Chapter_30_Interface.lean
lake env lean Tests/Chapter_30_DFT_Interface.lean
lake env lean Tests/Chapter_30_RecursiveFFT_Interface.lean
lake env lean Tests/Chapter_30_PolynomialMultiplication_Interface.lean
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
lake env lean Tests/Chapter_30_BitReversal_Interface.lean
lake env lean Tests/Chapter_30_IterativeFFT_Interface.lean
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
lake env lean Tests/Chapter_30_Milestone2_Closure.lean
```

Expected: all nine exit 0.

- [ ] **Step 5: Commit final source wiring**

```bash
git add CLRSLean/Chapter_30.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  literate.toml docs/index.md
git diff --cached --check
git commit -m "feat(ch30): expose efficient FFT implementations"
```

Stage `CLRSLean.lean` only when Step 3 found a real missing root import.

### Task 5: Close Proof Map And Status Truth

**Files:**
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-status-board.md` only when Chapter 30 still appears as active/incomplete
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`

- [ ] **Step 1: Inventory reviewed theorem groups**

Run:

```bash
rg -n '^#check ' Tests/Chapter_30_*.lean
```

Group aliases and closely related application/erasure views under one reviewed
result.  Count the new bit-reversal, stage invariant, iterative correctness,
execution cost, and circuit size/depth groups once each.  Record the resulting
integer consistently; do not count helper cast lemmas.

- [ ] **Step 2: Update the proof map**

Replace the Section 30.3 deferred paragraph with the actual theorem families,
including both cost conventions:

```text
execution arithmetic = 2*k*2^k
execution total = 2^k + 2*k*2^k
circuit butterflies = k*2^(k-1)
circuit primitive gates = 3*k*2^(k-1)
butterfly depth = k
primitive depth = 2*k
```

- [ ] **Step 3: Update the Chapter 30 CSV row and status page**

Set Chapter 30 to `proved`, represented sections `30.1;30.2;30.3`, and
`missing_core_groups` to zero.  Use the reviewed group count from Step 1 for
both tracked and proved fields.  Preserve the exact-arithmetic and functional
machine-model exclusions in notes/evidence.  Move Chapter 30 from partial to
proved in `CLRSLean/Status.lean` and remove it from active priorities when
present.

- [ ] **Step 4: Regenerate and check derived artifacts**

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
```

Expected: every command exits 0 and Chapter 30 is consistently `proved`.

- [ ] **Step 5: Commit status closure**

```bash
git add docs/proof-map.md docs/clrs-proof-progress.csv \
  CLRSLean/Status.lean CLRSLean/Progress.lean README.md
git diff --name-only --cached
git diff --cached --check
git commit -m "docs(ch30): close efficient FFT theorem groups"
```

Stage `docs/proof-status-board.md` only if intentionally changed in Step 3.

### Task 6: Run Final Verification And Create The Audit

**Files:**
- Create: `docs/proof-audits/chapter-30-milestone-2-2026-08-05.md`
- Modify: `docs/index.md`

- [ ] **Step 1: Read completion and review skills before claiming success**

Read completely:

```text
/home/ubuntu/.codex/superpowers/skills/verification-before-completion/SKILL.md
/home/ubuntu/.codex/superpowers/skills/requesting-code-review/SKILL.md
```

Apply their evidence and self-review checklists inline.  The approved execution
mode forbids subagents, so do not dispatch a reviewer agent.

- [ ] **Step 2: Run the complete fresh verification matrix**

Run all nine test commands from Task 4 again, followed by:

```bash
rg -n "sorryAx|sorry|admit" \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations.lean \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
uv run python scripts/check_repository.py
uv run python scripts/check_site_consistency.py
git diff --check
lake build CLRSLean
```

Expected: the unfinished-proof scan has no matches and every remaining command
exits 0.  Record actual job counts and elapsed evidence; do not predict them.
Website generation, rendering inspection, and deployment remain outside this
proof task unless the user explicitly requests a publishing task.

- [ ] **Step 3: Record the dated audit**

Create the audit with:

- approved scope and exclusions;
- the actual module and theorem inventory;
- all nine interface results;
- exact `#print axioms` output, naming accepted foundational axioms and
  confirming no `sorryAx` or project axiom;
- execution and circuit cost distinctions;
- repository/source-site-configuration/full-build commands with actual exit
  status and job counts;
  and
- the final reviewed theorem-group count and status-row evidence.

Register the audit in `docs/index.md`.

- [ ] **Step 4: Check, commit, and confirm a clean branch**

```bash
uv run python scripts/check_repository.py
git diff --check
git add docs/proof-audits/chapter-30-milestone-2-2026-08-05.md docs/index.md
git commit -m "docs(ch30): record efficient FFT closure audit"
git status --short --branch
```

Expected: repository check and diff check exit 0; final status prints only the
branch header with no changed paths.
