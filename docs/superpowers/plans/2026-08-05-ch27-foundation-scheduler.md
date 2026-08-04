# Chapter 27 Foundation and Scheduler Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Split the Chapter 27 multithreading model into focused modules, construct a terminating greedy scheduler for every finite computation DAG, and close the balanced parallel-loop logarithmic-depth theorem.

**Architecture:** Preserve every existing declaration in `CLRS.Chapter27` while turning `Section_27_1_Multithreading_Model.lean` into an aggregator.  A deterministic prefix of the sorted ready set supplies each greedy step; recursion on residual work constructs a completed `DAGSchedule`, which then reuses the existing accounting theorem.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `Finset`/`List` APIs, Lake, Verso module registration, CLRS-Lean interface tests.

---

## File Map

- Replace `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model.lean` with an aggregator and reader guide.
- Create `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S1_ComputationDAG.lean` for `Strand`, `CompDAG`, work, longest paths, and span.
- Create `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S2_ReadyExecution.lean` for residual work/span, `ready`, `execute`, and progress lemmas.
- Create `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S3_GreedyAccounting.lean` for accounting certificates, traces, concrete steps, and `DAGSchedule`.
- Create `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler.lean` for ready-prefix selection and total schedule construction.
- Create `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S5_SpawnTreeAndLoops.lean` for spawn trees and balanced parallel loops.
- Create `Tests/Chapter_27_Scheduler_Interface.lean` for the new executable scheduler and loop-depth surface.
- Modify `literate.toml` and `docs/index.md` to register the five submodules.

### Task 1: Record the Green Characterization Boundary

**Files:**
- Test: `Tests/Chapter_27_Interface.lean`

- [ ] **Step 1: Run the existing Chapter 27 interface before moving declarations**

Run:

```bash
lake env lean Tests/Chapter_27_Interface.lean
```

Expected: exit 0.  Save the output containing the current `#check` types and concrete DAG/loop examples for comparison after the split.

- [ ] **Step 2: Confirm the current source has no unfinished proofs**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_27/Section_27_1_Multithreading_Model.lean
```

Expected: no matches.

### Task 2: Split the Existing Section Without API Changes

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S1_ComputationDAG.lean`
- Create: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S2_ReadyExecution.lean`
- Create: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S3_GreedyAccounting.lean`
- Create: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler.lean`
- Create: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S5_SpawnTreeAndLoops.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Move the computation-DAG foundation into S1**

Move, without renaming, the declarations from `Strand` through
`CompDAG.span_le_work`.  Start the file with:

```lean
import Mathlib.Tactic

/-!
# 27.1 S1. Computation DAGs, work, and span

Defines weighted forward-edge computation DAGs and proves `T∞ ≤ T₁`.
-/

namespace CLRS
namespace Chapter27
```

Close the same namespaces at EOF.  Keep all existing doc comments.

- [ ] **Step 2: Move residual execution into S2**

Import S1 and move the declarations from `CompDAG.remainingWork` through
`CompDAG.remainingWork_execute_add_card`:

```lean
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S1_ComputationDAG
```

The public names and namespace nesting remain unchanged.

- [ ] **Step 3: Move accounting and certificate schedules into S3**

Import S2 and move `GreedyScheduleAccounting` through
`DAGSchedule.time_le_work_div_add_span`.  This includes
`GreedyScheduleTrace`, `GreedyScheduleRun`, `DAGScheduleStep`, and
`DAGSchedule`.

- [ ] **Step 4: Move spawn trees and loops into S5**

Import S1 and move `SpawnTree` through `parallelLoopDepth_pow`.

- [ ] **Step 5: Create the empty downstream scheduler module**

Create S4 with an import of S3, the standard Chapter 27 namespaces, and a
module doc comment explaining that executable schedule construction is added
in Task 4.  It must contain no admitted declaration.  Creating the module now
keeps the aggregator buildable while the RED interface remains genuinely RED.

- [ ] **Step 6: Replace the original file with the aggregator**

Use exactly these imports followed by an updated section guide:

```lean
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S5_SpawnTreeAndLoops
```

Do not import S4 from S3; S4 is the new downstream constructor layer.

- [ ] **Step 7: Register the new source modules**

Add all five module paths under Chapter 27 in `literate.toml`, in S1-S5 order,
and add matching titles.  Add the five file paths to the source catalog in
`docs/index.md`.

- [ ] **Step 8: Re-run the characterization test**

Run:

```bash
lake env lean Tests/Chapter_27_Interface.lean
uv run python scripts/check_repository.py
```

Expected: both exit 0 and every pre-split public name retains the same type.

- [ ] **Step 9: Commit the structural split**

```bash
git add CLRSLean/Chapter_27/Section_27_1_Multithreading_Model.lean \
  CLRSLean/Chapter_27/Section_27_1_Multithreading_Model \
  literate.toml docs/index.md
git commit -m "refactor(ch27): split multithreading model modules"
```

### Task 3: Lock the Executable Scheduler Interface in RED

**Files:**
- Create: `Tests/Chapter_27_Scheduler_Interface.lean`

- [ ] **Step 1: Add the intended scheduler checks**

Create the file with:

```lean
import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check CompDAG.readyRun
#check CompDAG.readyRun_subset_ready
#check CompDAG.readyRun_card
#check CompDAG.ready_nonempty_of_remainingWork_pos
#check CompDAG.greedyStep
#check CompDAG.greedyScheduleFrom
#check CompDAG.greedySchedule
#check CompDAG.greedySchedule_final_work_eq_zero
#check CompDAG.greedySchedule_time_le_work_div_add_span

end CLRS.Chapter27
```

- [ ] **Step 2: Verify the expected RED failure**

Run:

```bash
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
```

Expected: nonzero exit with `Unknown constant CLRS.Chapter27.CompDAG.readyRun`.

- [ ] **Step 3: Commit the red interface contract**

```bash
git add Tests/Chapter_27_Scheduler_Interface.lean
git commit -m "test(ch27): specify executable scheduler interface"
```

### Task 4: Implement Deterministic Ready-Set Selection

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler.lean`
- Test: `Tests/Chapter_27_Scheduler_Interface.lean`

- [ ] **Step 1: Define the executable ready prefix**

Start S4 by importing S3 and define:

```lean
namespace CLRS
namespace Chapter27
namespace CompDAG

/-- The first `processors` ready vertices in increasing vertex order. -/
def readyRun (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) : Finset ℕ :=
  (((G.ready remaining).sort (· ≤ ·)).take processors).toFinset
```

- [ ] **Step 2: Prove subset and cardinality equations**

Add:

```lean
theorem readyRun_subset_ready (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) :
    G.readyRun remaining processors ⊆ G.ready remaining := by
  -- Rewrite membership through `List.mem_toFinset`, `List.mem_take`, and
  -- `Finset.mem_sort`; then return the original ready-set membership.

theorem readyRun_card (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) :
    (G.readyRun remaining processors).card =
      min processors (G.ready remaining).card := by
  -- Use nodup of `Finset.sort`, `List.nodup_take`, `List.toFinset_card`,
  -- and `List.length_take`.
```

The implementation proof must use those library facts; it must not introduce
a cardinality axiom or a noncomputable arbitrary subset.

- [ ] **Step 3: Prove a ready vertex exists whenever work remains**

Add:

```lean
theorem ready_nonempty_of_remainingWork_pos (G : CompDAG)
    (remaining : ℕ → ℕ) (hwork : 0 < G.remainingWork remaining) :
    (G.ready remaining).Nonempty := by
  by_contra hempty
  have hdrop := G.remainingSpan_execute_ready_add_one_le remaining hwork
  have hready : G.ready remaining = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  simp [hready, CompDAG.execute] at hdrop
```

- [ ] **Step 4: Build one certified greedy step**

Add:

```lean
def greedyStep (G : CompDAG) (remaining : ℕ → ℕ) (processors : ℕ) :
    DAGScheduleStep G processors where
  remaining := remaining
  run := G.readyRun remaining processors
  run_subset_ready := G.readyRun_subset_ready remaining processors
  run_card_eq_min := G.readyRun_card remaining processors
```

- [ ] **Step 5: Compile the focused module**

Run:

```bash
lake build +CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S4_ExecutableScheduler
```

Expected: success.

### Task 5: Construct a Completed Schedule by Residual-Work Recursion

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler.lean`
- Modify: `Tests/Chapter_27_Scheduler_Interface.lean`

- [ ] **Step 1: Prove the chosen run is nonempty in an active state**

Add `readyRun_nonempty` with premises `0 < processors` and
`0 < G.remainingWork remaining`.  Rewrite `readyRun_card`, use
`ready_nonempty_of_remainingWork_pos`, and prove its cardinality is positive.

- [ ] **Step 2: Prove strict residual-work decrease**

Add:

```lean
theorem remainingWork_greedyStep_after_lt (G : CompDAG)
    (remaining : ℕ → ℕ) (processors : ℕ) (hp : 0 < processors)
    (hwork : 0 < G.remainingWork remaining) :
    G.remainingWork (G.greedyStep remaining processors).after <
      G.remainingWork remaining := by
  have hbalance := (G.greedyStep remaining processors).remainingWork_after_add_card
  have hrun := G.readyRun_nonempty remaining processors hp hwork
  omega
```

- [ ] **Step 3: Define the terminating schedule constructor**

Add a recursive definition with this public type:

```lean
def greedyScheduleFrom (G : CompDAG) (processors : ℕ) (hp : 0 < processors) :
    (remaining : ℕ → ℕ) → DAGSchedule G processors remaining
```

Its zero-work branch is `DAGSchedule.done`; its active branch creates
`G.greedyStep remaining processors` and recurses on `.after`.  Use
`G.remainingWork remaining` as `termination_by` and
`remainingWork_greedyStep_after_lt` for the decreasing obligation.

Add the initial-state wrapper:

```lean
def greedySchedule (G : CompDAG) (processors : ℕ) (hp : 0 < processors) :
    DAGSchedule G processors G.node_work :=
  G.greedyScheduleFrom processors hp G.node_work
```

- [ ] **Step 4: Add completion and scheduler-bound wrappers**

```lean
theorem greedySchedule_final_work_eq_zero (G : CompDAG) (processors : ℕ)
    (hp : 0 < processors) :
    G.remainingWork (G.greedySchedule processors hp).finalState = 0 :=
  (G.greedySchedule processors hp).final_work_eq_zero

theorem greedySchedule_time_le_work_div_add_span (G : CompDAG)
    (processors : ℕ) (hp : 0 < processors) :
    (G.greedySchedule processors hp).time ≤
      G.work / processors + G.span :=
  (G.greedySchedule processors hp).time_le_work_div_add_span hp
```

- [ ] **Step 5: Exercise real schedules in the interface**

Add a local one-node DAG and examples asserting by `native_decide` that the
constructed schedule has time one, final residual work zero, and satisfies the
bound.  Add a two-branch fork example with processor counts one and two.

- [ ] **Step 6: Run GREEN checks and commit**

```bash
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
git add CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler.lean \
  Tests/Chapter_27_Scheduler_Interface.lean
git commit -m "feat(ch27): construct terminating greedy schedules"
```

Expected: test exits 0.

### Task 6: Prove the Missing Parallel-Loop Upper Bound

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S5_SpawnTreeAndLoops.lean`
- Modify: `Tests/Chapter_27_Scheduler_Interface.lean`

- [ ] **Step 1: Extend the interface and verify RED**

Append these checks to `Tests/Chapter_27_Scheduler_Interface.lean`:

```lean
#check parallelLoopDepth_le_log
#check parallelLoop_span_le_log
```

Run the focused test and expect a nonzero exit at
`CLRS.Chapter27.parallelLoopDepth_le_log`.  The already implemented scheduler
checks must resolve before that failure.

- [ ] **Step 2: Add the logarithmic helper statement**

Prove a private natural-arithmetic lemma for `2 ≤ n`:

```lean
private theorem log_ceil_half_add_one_le_log (n : ℕ) (hn : 2 ≤ n) :
    Nat.log 2 (n - n / 2) + 1 ≤ Nat.log 2 n := by
  -- Bound the ceiling half by `2 ^ Nat.log 2 n`, then apply
  -- `Nat.le_log_of_pow_le`; isolate parity arithmetic with `omega`.
```

- [ ] **Step 3: Prove depth monotonicity and the public upper bound**

Use strong induction to establish that the floor-half depth is no larger than
the ceiling-half depth, then prove:

```lean
theorem parallelLoopDepth_le_log (n : ℕ) :
    parallelLoopDepth n ≤ Nat.log 2 n + 1 := by
  -- Base cases `n ≤ 1`; otherwise unfold, apply both strong-induction
  -- hypotheses, and close the logarithm step with the helper above.
```

- [ ] **Step 4: Package the loop-span theorem**

```lean
theorem parallelLoop_span_le_log (n w : ℕ) :
    (parallelLoopTree n w).span ≤ w + Nat.log 2 n + 1 := by
  rw [parallelLoop_span]
  split_ifs with hn
  · omega
  · have := parallelLoopDepth_le_log n
    omega
```

- [ ] **Step 5: Add concrete boundary examples**

Check depths for `0, 1, 2, 3, 8, 9` with `native_decide`, and instantiate the
upper-bound theorem at `n = 9`.

- [ ] **Step 6: Run tests and commit**

```bash
lake build +CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S5_SpawnTreeAndLoops
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
git add CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S5_SpawnTreeAndLoops.lean \
  Tests/Chapter_27_Scheduler_Interface.lean
git commit -m "feat(ch27): close parallel-loop logarithmic span"
```

### Task 7: Verify the Foundation Phase

**Files:**
- All files changed in this plan.

- [ ] **Step 1: Run focused and static gates**

```bash
lake env lean Tests/Chapter_27_Interface.lean
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_27/Section_27_1_Multithreading_Model -g '*.lean'
uv run python scripts/check_repository.py
git diff --check
```

Expected: both Lean tests and repository checks exit 0; the unfinished-proof scan
has no matches; `git diff --check` is silent.

- [ ] **Step 2: Record the phase checkpoint**

```bash
git status --short
git log -4 --oneline
```

Expected: no uncommitted scheduler-phase files and separate commits for the
module split, RED interface, scheduler, and loop bound.
