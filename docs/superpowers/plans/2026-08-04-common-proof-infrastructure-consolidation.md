# Common Proof Infrastructure Consolidation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give recurring finite-expectation, adjacent-power, fiber, and interval proofs one canonical implementation while preserving every established chapter-facing theorem statement.

**Architecture:** Canonical algebra stays in the narrowest existing owner (`Probability`, Chapter 4); generic geometric lemmas stay in `ProofPatterns`; consuming chapters expose exact bridges and compatibility wrappers. Progress records textbook theorem groups, so helpers, bridges, aliases, and wrappers do not increase counts.

**Tech Stack:** Lean 4, Mathlib, Lake, Python repository checks

---

## Task 1: Freeze the intended public interface as a red test

**Files:**
- Create: `Tests/Common_Proof_Infrastructure.lean`

- [ ] **Step 1: Add imports and checks for all canonical helpers and bridges**

```lean
import CLRSLean.Probability.FiniteExpectation
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
import CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing
import CLRSLean.Chapter_22.Section_22_3_DFS.S2_Intervals
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms

#check CLRS.Probability.fintypeExpect_mono
#check CLRS.Probability.fintypeExpect_neg
#check CLRS.Chapter04.monotoneAbs_natCast
#check CLRS.Chapter04.monotone_power_sandwich
#check CLRS.Chapter08.bucket_eq_fiber
#check CLRS.Chapter22.Graph.dfsInterval
#check CLRS.Chapter22.Graph.finishesBeforeDiscovered_iff_strictlyBefore
#check CLRS.Chapter22.Graph.intervalNestedInside_iff_nestedInside
#check CLRS.Chapter05.fintypeExpect_mono
#check CLRS.Chapter11.fintypeExpect_mono
#check CLRS.Chapter11.fintypeExpect_neg
```

Add small `example` terms for the Chapter 5 redundant-hypothesis wrapper, the Chapter 27 adjacent-power shape, the bucket/fiber equality, and DFS nesting asymmetry. This makes the test check usable theorem shapes rather than name existence alone.

- [ ] **Step 2: Run the focused test and record the expected failure**

Run: `lake env lean Tests/Common_Proof_Infrastructure.lean`

Expected: failure on the new canonical and bridge names; existing compatibility names still elaborate.

- [ ] **Step 3: Commit the red interface contract**

```bash
git add Tests/Common_Proof_Infrastructure.lean
git commit -m "test(proofs): specify shared infrastructure interface"
```

## Task 2: Canonicalize finite-expectation algebra

**Files:**
- Modify: `CLRSLean/Probability/FiniteExpectation.lean`
- Modify: `CLRSLean/Chapter_05/Section_05_4_Probabilistic_Analysis.lean`
- Modify: `CLRSLean/Chapter_11/Section_11_5_Perfect_Hashing.lean`
- Test: `Tests/Common_Proof_Infrastructure.lean`
- Test: `Tests/Chapter_05_Interface.lean`

- [ ] **Step 1: Add canonical monotonicity and negation theorems beside the existing generic algebra**

```lean
/-- Pointwise order is preserved by finite uniform expectation. -/
theorem fintypeExpect_mono {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {X Y : Ω → ℝ} (hXY : ∀ ω, X ω ≤ Y ω) :
    fintypeExpect X ≤ fintypeExpect Y := by
  unfold fintypeExpect
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => hXY ω) ?_
  positivity

/-- Finite uniform expectation commutes with pointwise negation. -/
theorem fintypeExpect_neg {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (X : Ω → ℝ) : fintypeExpect (fun ω => -X ω) = -fintypeExpect X := by
  simp [fintypeExpect, Finset.sum_neg_distrib, neg_div]
```

- [ ] **Step 2: Replace Chapter 5's proof body with a compatibility delegation**

Keep the existing statement, including `hX` and `hY`, unchanged:

```lean
  clear hX hY
  exact Probability.fintypeExpect_mono hXY
```

- [ ] **Step 3: Replace Chapter 11's two proof bodies with compatibility delegations**

```lean
  exact Probability.fintypeExpect_mono hXY
```

and

```lean
  exact Probability.fintypeExpect_neg X
```

- [ ] **Step 4: Run focused builds**

```bash
lake env lean CLRSLean/Probability/FiniteExpectation.lean
lake env lean CLRSLean/Chapter_05/Section_05_4_Probabilistic_Analysis.lean
lake env lean CLRSLean/Chapter_11/Section_11_5_Perfect_Hashing.lean
lake env lean Tests/Chapter_05_Interface.lean
```

Expected: success, with no changed chapter-facing theorem type.

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/Probability/FiniteExpectation.lean \
  CLRSLean/Chapter_05/Section_05_4_Probabilistic_Analysis.lean \
  CLRSLean/Chapter_11/Section_11_5_Perfect_Hashing.lean
git commit -m "refactor(probability): canonicalize finite expectation algebra"
```

## Task 3: Promote adjacent-power transfer helpers and migrate Chapter 27

**Files:**
- Modify: `CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`
- Modify: `Tests/Chapter_04_Interface.lean`
- Modify: `Tests/Chapter_27_Interface.lean`
- Test: `Tests/Common_Proof_Infrastructure.lean`

- [ ] **Step 1: Add the natural-cost cast adapter after `MonotoneAbs`**

```lean
/-- A monotone natural-valued cost is monotone after casting to real absolute values. -/
theorem monotoneAbs_natCast {T : ℕ → ℕ} (hT : Monotone T) :
    MonotoneAbs (fun n => (T n : ℝ)) := by
  intro m n hmn
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  change (T m : ℝ) ≤ (T n : ℝ)
  exact_mod_cast hT hmn
```

- [ ] **Step 2: Map the adjacent-power interval through any monotone natural-valued function**

Place this immediately after `powerInterval_of_pos`:

```lean
/-- Mapping the adjacent-power interval through a monotone natural-valued cost. -/
theorem monotone_power_sandwich {T : ℕ → ℕ} (hT : Monotone T)
    (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) :
    T (b ^ Nat.log b n) ≤ T n ∧
      T n ≤ T (b ^ (Nat.log b n + 1)) := by
  rcases powerInterval_of_pos b n hb hn with ⟨hlo, hhi⟩
  exact ⟨hT hlo, hT (Nat.le_of_lt hhi)⟩
```

- [ ] **Step 3: Delete Chapter 27's two private helpers and use Chapter 4 directly**

Replace every local call with:

```lean
Chapter04.monotone_power_sandwich COST_monotone 2 n (by norm_num) hn.ne'
```

and every monotonicity adapter with:

```lean
Chapter04.monotoneAbs_natCast COST_monotone
```

- [ ] **Step 4: Extend the existing Chapter 4 and 27 interface checks**

Add `#check` lines for the two shared helpers to Chapter 4. Keep Chapter 27's six reader-facing sandwich and all-input checks, adding an example that calls the Chapter 4 generic theorem with a Chapter 27 cost.

- [ ] **Step 5: Run focused builds and interfaces**

```bash
lake env lean CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean
lake env lean CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean
lake env lean Tests/Chapter_04_Interface.lean
lake env lean Tests/Chapter_27_Interface.lean
```

- [ ] **Step 6: Commit**

```bash
git add CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_04_Interface.lean Tests/Chapter_27_Interface.lean
git commit -m "refactor(master): share adjacent-power transfer helpers"
```

## Task 4: Bridge Chapter 8 buckets to generic fibers

**Files:**
- Modify: `CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean`
- Modify: `Tests/Chapter_08_Interface.lean`
- Test: `Tests/Common_Proof_Infrastructure.lean`

- [ ] **Step 1: Import the generic Fiber module and add the exact bridge**

```lean
import CLRSLean.ProofPatterns.Fiber

/-- Counting-sort buckets are exactly the generic key fibers. -/
theorem bucket_eq_fiber (key : α → Nat) (xs : List α) (k : Nat) :
    bucket key xs k = ProofPatterns.fiber key xs k := by
  simp [bucket, ProofPatterns.fiber]
```

- [ ] **Step 2: Delegate the matching local theorem bodies**

Rewrite `bucket_append`, `mem_bucket_iff`, `bucket_all_keys_eq`, and `bucket_bucket_eq` by transporting the corresponding `ProofPatterns.fiber_*` theorem through `bucket_eq_fiber`. Preserve all four statements and public names exactly.

- [ ] **Step 3: Extend the Chapter 8 interface with the bridge and a generic-fiber use example**

- [ ] **Step 4: Run focused builds**

```bash
lake env lean CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean
lake env lean Tests/Chapter_08_Interface.lean
```

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean Tests/Chapter_08_Interface.lean
git commit -m "refactor(counting-sort): bridge buckets to generic fibers"
```

## Task 5: Bridge Chapter 22 DFS timestamps to generic intervals

**Files:**
- Modify: `CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals.lean`
- Modify: `Tests/Chapter_22_Interface.lean`
- Test: `Tests/Common_Proof_Infrastructure.lean`

- [ ] **Step 1: Import the generic Interval module and define the projection**

```lean
import CLRSLean.ProofPatterns.Interval

/-- The discovery/finish timestamp interval of a vertex in a DFS state. -/
def dfsInterval (s : DFSState V) (u : V) : ProofPatterns.NatInterval where
  lo := discoveryTime s u
  hi := finishTime s u
```

- [ ] **Step 2: Add exact representation bridges**

```lean
theorem finishesBeforeDiscovered_iff_strictlyBefore
    (s : DFSState V) (u v : V) :
    finishesBeforeDiscovered s u v ↔
      ProofPatterns.NatInterval.StrictlyBefore (dfsInterval s u) (dfsInterval s v) :=
  Iff.rfl

theorem intervalNestedInside_iff_nestedInside
    (s : DFSState V) (u v : V) :
    intervalNestedInside s u v ↔
      ProofPatterns.NatInterval.NestedInside (dfsInterval s v) (dfsInterval s u) :=
  Iff.rfl
```

- [ ] **Step 3: Expose one useful DFS-facing algebra consequence**

Add `intervalNestedInside_asymm`, proved by converting the hypothesis and conclusion with `intervalNestedInside_iff_nestedInside` and invoking `NatInterval.nestedInside_asymm`. This establishes a real consumer without rewriting the parenthesis stack.

- [ ] **Step 4: Extend and run the Chapter 22 interface**

```bash
lake env lean CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals.lean
lake env lean Tests/Chapter_22_Interface.lean
```

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals.lean Tests/Chapter_22_Interface.lean
git commit -m "refactor(dfs): bridge timestamps to generic intervals"
```

## Task 6: Turn the red common interface test green and document ownership

**Files:**
- Modify: `Tests/Common_Proof_Infrastructure.lean`
- Create: `docs/proof-patterns/common-proof-library-decision-matrix.md`
- Modify: `docs/proof-patterns/geometric-proof-patterns.md`
- Modify: `docs/repository-architecture.md`

- [ ] **Step 1: Finalize executable examples in the common test**

The test must demonstrate:

- canonical expectation monotonicity and negation;
- the unchanged Chapter 5 and 11 wrapper shapes;
- Chapter 4's generic theorem instantiated with a Chapter 27 cost;
- `bucket_eq_fiber` used in a concrete list expression;
- DFS interval nesting asymmetry obtained through the shared interval algebra.

- [ ] **Step 2: Run the common test and all affected interfaces**

```bash
lake env lean Tests/Common_Proof_Infrastructure.lean
lake env lean Tests/Chapter_04_Interface.lean
lake env lean Tests/Chapter_05_Interface.lean
lake env lean Tests/Chapter_08_Interface.lean
lake env lean Tests/Chapter_22_Interface.lean
lake env lean Tests/Chapter_27_Interface.lean
```

- [ ] **Step 3: Add the decision matrix**

Document each candidate with canonical owner, current consumers, compatibility surface, progress-count treatment, and extraction threshold. Mark Probability, Chapter 4, Chapter 17, Fiber, and Interval as active; Boundary and Exchange as deferred; local surgery and DP grids as atlas-only.

- [ ] **Step 4: Update the atlas and repository architecture**

Record Chapter 8 and Chapter 22 as actual Fiber/Interval consumers. Distinguish domain libraries, demonstrated geometric patterns, and pedagogical/deferred patterns. Add the theorem-group counting rule: a shared theorem is counted once, wrappers/aliases/bridges never add counts, and chapter instances count only distinct textbook obligations.

- [ ] **Step 5: Confirm no progress ledger moved**

Run: `git diff --name-only $(git merge-base HEAD origin/main)..HEAD | rg 'clrs-proof-progress|Progress\.lean|proof-status-board'`

Expected: no output.

- [ ] **Step 6: Commit**

```bash
git add Tests/Common_Proof_Infrastructure.lean \
  docs/proof-patterns/common-proof-library-decision-matrix.md \
  docs/proof-patterns/geometric-proof-patterns.md docs/repository-architecture.md
git commit -m "docs(proofs): record common library ownership and counting"
```

## Task 7: Axiom audit and final verification

**Files:**
- Create temporarily, then remove: `Tests/Common_Proof_Infrastructure_Axioms.lean`
- Verify all changed Lean and documentation files

- [ ] **Step 1: Audit canonical theorem dependencies**

Create a temporary audit importing the focused modules and printing axioms for:

```lean
#print axioms CLRS.Probability.fintypeExpect_mono
#print axioms CLRS.Probability.fintypeExpect_neg
#print axioms CLRS.Chapter04.monotoneAbs_natCast
#print axioms CLRS.Chapter04.monotone_power_sandwich
#print axioms CLRS.Chapter08.bucket_eq_fiber
#print axioms CLRS.Chapter22.Graph.intervalNestedInside_asymm
```

Run it with `lake env lean`, inspect for `sorryAx` or project axioms, then delete the temporary file.

- [ ] **Step 2: Scan changed Lean files for placeholders**

```bash
git diff --name-only $(git merge-base HEAD origin/main)..HEAD -- '*.lean' \
  | xargs rg -n '\b(sorry|admit)\b' || true
```

Expected: no placeholders in changed Lean files.

- [ ] **Step 3: Run formatting and repository metadata checks**

```bash
git diff --check
uv run python scripts/check_repository.py
```

- [ ] **Step 4: Run the final Lean aggregate only**

Run: `lake build CLRSLean`

Expected: success. Existing linter warnings are acceptable; no website/HTML target is built.

- [ ] **Step 5: Review the complete branch diff and commit any verification-only cleanup**

```bash
git status --short
git log --oneline --decorate -8
git diff --stat $(git merge-base HEAD origin/main)..HEAD
```

If cleanup was required, commit it as:

```bash
git add <exact-cleanup-files>
git commit -m "test(proofs): seal common infrastructure consolidation"
```

The branch is ready for review only when the worktree is clean and every command above has fresh successful output.
