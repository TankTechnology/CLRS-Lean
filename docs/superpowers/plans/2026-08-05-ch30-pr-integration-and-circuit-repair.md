# Chapter 30 PR Integration And Circuit Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rebuild PR #154 on current `origin/main` and make its FFT circuit evaluation, gate enumeration, size, and depth share one verified representation.

**Architecture:** Migrate only Chapter 30-owned artifacts into a clean branch, then integrate shared metadata against current `main`.  Add individual butterfly gates, gate-family layers, and recursive stage-circuit syntax; make the network evaluate and count that syntax, with bridge theorems back to the verified iterative FFT.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib, CLRS-Lean `PowTwoVec`/iterative FFT interfaces, Lake, Python repository checks, Git.

---

### Task 1: Migrate The Existing Chapter 30 Boundary

**Files:**

- Create: `CLRSLean/Chapter_30.lean`
- Create: `CLRSLean/Chapter_30/**`
- Create: `Tests/Chapter_30_*.lean`
- Create: `docs/superpowers/specs/2026-08-05-chapter-30-*.md`
- Create: `docs/superpowers/plans/2026-08-05-ch30-*.md`
- Create: `docs/proof-audits/chapter-30-*.md`

- [x] **Step 1: Apply only Chapter 30-owned files from the stale branch**

Use a path-restricted binary diff from `codex/ch30fight`; do not cherry-pick its
unrelated Chapter 4--27 or common-infrastructure history.

```bash
git diff --binary origin/main...codex/ch30fight -- \
  CLRSLean/Chapter_30.lean CLRSLean/Chapter_30 \
  'Tests/Chapter_30_*.lean' \
  'docs/superpowers/specs/2026-08-05-chapter-30-*' \
  'docs/superpowers/plans/2026-08-05-ch30-*' \
  'docs/proof-audits/chapter-30-*' | git apply
```

Expected: only Chapter 30-owned files appear as additions.

- [x] **Step 2: Run the nine migrated tests before changing semantics**

```bash
lake build +CLRSLean.Chapter_30
for test in Tests/Chapter_30_*.lean; do lake env lean "$test"; done
```

Expected: the Chapter 30 module builds and all nine tests exit zero on current
`main` dependencies.

- [x] **Step 3: Commit the isolated source migration**

```bash
git add CLRSLean/Chapter_30.lean CLRSLean/Chapter_30 Tests/Chapter_30_*.lean \
  docs/superpowers/specs/2026-08-05-chapter-30-* \
  docs/superpowers/plans/2026-08-05-ch30-* \
  docs/proof-audits/chapter-30-*
git commit -m "feat(ch30): migrate verified FFT formalization"
```

### Task 2: Integrate Current Repository Owners

**Files:**

- Modify: `CLRSLean.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`
- Modify: `docs/index.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`
- Modify: `literate.toml`
- Modify: `CLAUDE.md`
- Modify: `.codex/skills/clrs-chapter-formalization/SKILL.md`
- Modify: `docs/workflows/chapter-workflow.md`

- [x] **Step 1: Wire Chapter 30 into the current root and source navigation**

Add the Chapter 30 root import after Chapter 29 and before Chapter 31.  Add the
chapter guide and all Section 30.1--30.3 modules to `literate.toml` and
`docs/index.md` in numerical order, without replacing the current Chapter 31
entries.

- [x] **Step 2: Merge the status truth against current `main`**

Add the reviewed Chapter 30 proof-map inventory and the CSV row values from the
Milestone 2 audit while preserving the completed Chapter 27--29 and 31 rows.
Keep exercises, Problems 30-1--30-6, and machine refinements explicitly outside
the denominator.  Remove Chapter 30 from active gaps if present.

- [x] **Step 3: Regenerate generated owners**

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py --write
```

Expected: totals are derived from the merged CSV rather than copied from the
stale branch.

- [x] **Step 4: Apply the proof-work publishing boundary**

Port only the approved wording that proof tasks do not authorize HTML
generation or deployment.  Preserve other current versions of the three policy
files.

- [x] **Step 5: Verify and commit repository integration**

```bash
uv run python scripts/check_repository.py
git diff --check
git add CLRSLean.lean CLRSLean/Status.lean CLRSLean/Progress.lean README.md \
  docs/clrs-proof-progress.csv docs/index.md docs/proof-map.md \
  docs/proof-status-board.md literate.toml CLAUDE.md \
  .codex/skills/clrs-chapter-formalization/SKILL.md \
  docs/workflows/chapter-workflow.md
git commit -m "docs(ch30): integrate current repository status"
```

### Task 3: Write The Circuit-Semantics RED Interface

**Files:**

- Modify: `Tests/Chapter_30_ParallelFFT_Interface.lean`

- [x] **Step 1: Add the wished-for public interface**

Add checks for these exact declarations:

```lean
#check FFTButterflyGate
#check FFTButterflyGate.eval
#check ButterflyLayerCircuit
#check ButterflyLayerCircuit.eval
#check canonicalButterflyLayerCircuit
#check canonicalButterflyLayerCircuit_eval
#check FFTStageCircuit
#check FFTStageCircuit.eval
#check FFTStageCircuit.butterflyCount
#check FFTStageCircuit.butterflyDepth
#check fftStageCircuit
#check fftStageCircuit_eval
#check fftStageCircuit_butterflyCount
#check fftStageCircuit_butterflyDepth
#check FFTLayer.eval
```

- [x] **Step 2: Confirm RED for the expected missing declaration**

```bash
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
```

Expected: nonzero exit with `Unknown identifier FFTButterflyGate`; imports must
otherwise resolve.

### Task 4: Implement Individual Gates And Butterfly Layers

**Files:**

- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean`
- Test: `Tests/Chapter_30_ParallelFFT_Interface.lean`

- [x] **Step 1: Define an evaluated logical butterfly gate**

```lean
structure FFTButterflyGate (K : Type*) where
  twiddle : K

def FFTButterflyGate.eval [Ring K] (gate : FFTButterflyGate K)
    (u v : K) : K × K :=
  let product := gate.twiddle * v
  (u + product, u - product)
```

- [x] **Step 2: Define the actual gate family for one local layer**

```lean
structure ButterflyLayerCircuit (K : Type*) (k : Nat) where
  gates : Fin (2 ^ k) -> FFTButterflyGate K

def canonicalButterflyLayerCircuit [Monoid K] (omega : K) (k : Nat) :
    ButterflyLayerCircuit K k :=
  { gates := fun j => { twiddle := omega ^ j.1 } }
```

Define `ButterflyLayerCircuit.eval` by applying `gates j` to `u j` and `v j`
for every `j`, then joining the first and second outputs.  Prove
`canonicalButterflyLayerCircuit_eval` by extensionality over the lower and
upper halves using `butterflyLayer_lower` and `butterflyLayer_upper`.

- [x] **Step 3: Run the narrow source and interface checks**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.ParallelFFT
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
```

Expected: remaining RED failures name `FFTStageCircuit`, not the gate/layer
declarations.

### Task 5: Implement The Recursive Stage Circuit

**Files:**

- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean`
- Test: `Tests/Chapter_30_ParallelFFT_Interface.lean`

- [x] **Step 1: Add syntax mirroring `fftStage`**

```lean
inductive FFTStageCircuit (K : Type*) : Nat -> Type _
  | butterfly {k : Nat} (layer : ButterflyLayerCircuit K k) :
      FFTStageCircuit K (k + 1)
  | parallel {k : Nat} (lower upper : FFTStageCircuit K k) :
      FFTStageCircuit K (k + 1)
```

Define structural `eval`, `butterflyCount`, and `butterflyDepth`.  A butterfly
node evaluates its gate family, contributes `2 ^ k` butterflies, and has depth
one.  A parallel node evaluates children on the two halves, sums counts, and
takes the maximum depth.

- [x] **Step 2: Build and prove the canonical stage**

Define `fftStageCircuit omega s` by the same final/nonfinal recursion as
`fftStageExec`: the final case is a canonical butterfly layer; the nonfinal
case is two canonical child circuits at `omega ^ 2`.

Prove:

```lean
theorem fftStageCircuit_eval [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) (s : Fin k) :
    (fftStageCircuit omega s).eval a = fftStage omega a s

theorem fftStageCircuit_butterflyCount {K : Type*} [Monoid K]
    {k : Nat} (omega : K) (s : Fin k) :
    (fftStageCircuit omega s).butterflyCount = 2 ^ (k - 1)

theorem fftStageCircuit_butterflyDepth {K : Type*} [Monoid K]
    {k : Nat} (omega : K) (s : Fin k) :
    (fftStageCircuit omega s).butterflyDepth = 1
```

- [x] **Step 3: Verify GREEN and commit the semantic core**

```bash
lake build +CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.ParallelFFT
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean \
  Tests/Chapter_30_ParallelFFT_Interface.lean
git commit -m "fix(ch30): attach FFT stages to evaluated gates"
```

### Task 6: Make Network Semantics And Costs Structural

**Files:**

- Modify: `CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean`
- Modify: `Tests/Chapter_30_ParallelFFT_Interface.lean`
- Modify: `Tests/Chapter_30_Milestone2_Closure.lean`

- [x] **Step 1: Make each `FFTLayer` own its circuit**

Add `circuit : FFTStageCircuit K k` to `FFTLayer`; canonical `fftLayer omega s`
stores `fftStageCircuit omega s`.  Define `FFTLayer.eval` using the circuit.
Change `FFTNetwork.evalPrefix` to call `layer.eval previous`.

- [x] **Step 2: Derive size and depth from stored syntax**

Define layer butterfly count/depth from `layer.circuit`.  Define network count
and depth as sums over stored layers.  Keep primitive gate count as three times
structural butterfly count and primitive depth as twice structural butterfly
depth.  Reprove the existing canonical closed forms.

- [x] **Step 3: Extend closure axiom evidence**

Print axioms for `fftStageCircuit_eval`, `fftNetwork_eval`,
`fftNetwork_butterflyCount`, and `fftNetwork_primitiveDepth` in the Milestone 2
closure test.

- [x] **Step 4: Run the focused GREEN gate and commit**

```bash
lake env lean Tests/Chapter_30_ParallelFFT_Interface.lean
lake env lean Tests/Chapter_30_Milestone2_Closure.lean
git diff --check
git add CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean \
  Tests/Chapter_30_ParallelFFT_Interface.lean Tests/Chapter_30_Milestone2_Closure.lean
git commit -m "fix(ch30): derive FFT network bounds from circuit syntax"
```

### Task 7: Refresh Audit And Run Final Verification

**Files:**

- Modify: `docs/proof-audits/chapter-30-milestone-2-2026-08-05.md`
- Modify only if theorem-group inventory changes: `docs/proof-map.md`
- Modify only if reviewed counts change: `docs/clrs-proof-progress.csv`,
  `CLRSLean/Progress.lean`, `README.md`, `CLRSLean/Status.lean`

- [x] **Step 1: Record the repaired circuit representation and exclusions**

Add the gate-to-stage bridge, structural counts, exact verification commands,
and the unchanged exclusions for exercises, Problems 30-1--30-6, machine
refinements, and website work.

- [x] **Step 2: Run every Chapter 30 test**

```bash
for test in Tests/Chapter_30_*.lean; do lake env lean "$test"; done
```

Expected: all nine exit zero.

- [x] **Step 3: Run closure and placeholder checks**

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_30 Tests/Chapter_30_*.lean
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
lake env lean Tests/Chapter_30_Milestone2_Closure.lean
```

Expected: the source scan has no forbidden declaration; closure output has no
`sorryAx` or project-defined axiom.

- [x] **Step 4: Run repository and full proof-build gates**

```bash
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
uv run python scripts/check_repository.py
git diff --check
lake build CLRSLean
```

Expected: every command exits zero.  Do not run `lake build :literateHtml`.

- [x] **Step 5: Commit the audit**

```bash
git add docs/proof-audits/chapter-30-milestone-2-2026-08-05.md \
  docs/proof-map.md docs/clrs-proof-progress.csv CLRSLean/Progress.lean \
  README.md CLRSLean/Status.lean
git commit -m "docs(ch30): record repaired circuit closure"
```

- [x] **Step 6: Stop before replacing the remote PR history**

Report the clean local branch, commits, test evidence, and proposed
`git push --force-with-lease origin codex/ch30-pr-clean:codex/ch30fight`.
Do not perform that remote history replacement without explicit user approval.
