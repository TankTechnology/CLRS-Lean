# Ch20.3 Recursive vEB Deletion Correctness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the false unconditional `VEBTreeMM.delete_toFinset` theorem with a kernel-checked deletion refinement theorem over a semantic representation invariant, including invariant preservation and public interface coverage.

**Architecture:** `MinCorrect` and `MaxCorrect` relate cached extrema to `toFinset`; structural `WellFormed` additionally makes summary membership exactly track nonempty clusters and detaches the stored minimum from cluster payloads. A strong induction over the universe level proves `delete_correct`, bundling preservation and `Finset.erase` semantics so recursive minimum/maximum tests can use the preserved invariant.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `Finset`/`Option` APIs, `omega`, CLRS-Lean interface tests, Verso documentation.

---

## File map

- Modify `Tests/Chapter_20_Interface.lean`: require the new invariant and deletion theorem surface.
- Modify `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`: define semantic invariants, prove helper lemmas, replace the five-sorry theorem with bundled deletion correctness and projections.
- Modify `CLRSLean/Chapter_20.lean`: report deletion correctness as proved while retaining the precise successor/predecessor/cost gap.
- Modify `docs/proof-map.md`: list the new public theorems and narrow the remaining gap.
- Modify `docs/clrs-proof-progress.csv`: add the recursive deletion correctness group and move the Chapter 20 counts from 152/152 to 153/153.
- Regenerate `CLRSLean/Progress.lean` from the CSV when the row changes.

### Task 1: Establish the failing public interface

**Files:**

- Modify: `Tests/Chapter_20_Interface.lean:143-170`

- [x] **Step 1: Add the intended public names**

Append these checks to the Section 20.3 block:

```lean
#check CLRS.Chapter20.VEBTreeMM.MinCorrect
#check CLRS.Chapter20.VEBTreeMM.MaxCorrect
#check CLRS.Chapter20.VEBTreeMM.WellFormed
#check CLRS.Chapter20.VEBTreeMM.empty_wellFormed
#check CLRS.Chapter20.VEBTreeMM.delete_correct
#check CLRS.Chapter20.VEBTreeMM.delete_wellFormed
#check CLRS.Chapter20.VEBTreeMM.delete_toFinset
```

- [x] **Step 2: Verify the red state**

Run:

```bash
lake env lean Tests/Chapter_20_Interface.lean
```

Expected: failure because `MinCorrect` (and the other new declarations) do not exist.

- [x] **Step 3: Commit the interface test**

```bash
git add Tests/Chapter_20_Interface.lean
git commit -m "test(ch20.3): require recursive deletion correctness interface"
```

### Task 2: Add semantic extrema predicates and proof projections

**Files:**

- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean:844-868`

- [x] **Step 1: Define the predicates before deletion correctness**

Add documented definitions:

```lean
def MinCorrect (mn : Option Nat) (s : Finset Nat) : Prop :=
  match mn with
  | none => s = ∅
  | some m => m ∈ s ∧ ∀ y ∈ s, m ≤ y

def MaxCorrect (mx : Option Nat) (s : Finset Nat) : Prop :=
  match mx with
  | none => s = ∅
  | some m => m ∈ s ∧ ∀ y ∈ s, y ≤ m
```

- [x] **Step 2: Prove the exact Option/Finset bridge family**

Add documented lemmas with these statements:

```lean
theorem MinCorrect.none_iff {mn s} (h : MinCorrect mn s) :
    mn = none ↔ s = ∅
theorem MinCorrect.mem {m s} (h : MinCorrect (some m) s) : m ∈ s
theorem MinCorrect.le {m y s} (h : MinCorrect (some m) s) (hy : y ∈ s) : m ≤ y

theorem MaxCorrect.none_iff {mx s} (h : MaxCorrect mx s) :
    mx = none ↔ s = ∅
theorem MaxCorrect.mem {m s} (h : MaxCorrect (some m) s) : m ∈ s
theorem MaxCorrect.le {m y s} (h : MaxCorrect (some m) s) (hy : y ∈ s) : y ≤ m
```

- [x] **Step 3: Build the section**

Run `lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB`.

Expected: the new definitions and lemmas compile; the old five `sorry` warnings remain.

### Task 3: Define structural well-formedness and prove empty

**Files:**

- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`

- [x] **Step 1: Define `WellFormed` structurally**

Use the following clause shape:

```lean
def WellFormed : ∀ {k : Nat}, VEBTreeMM k → Prop
  | _, v@(.leaf mn mx _ _) =>
      MinCorrect mn v.toFinset ∧ MaxCorrect mx v.toFinset
  | _, v@(@VEBTreeMM.node k mn mx summary clusters) =>
      MinCorrect mn v.toFinset ∧
      MaxCorrect mx v.toFinset ∧
      (∀ m, mn = some m → ∀ hi lo, lo ∈ (clusters hi).toFinset →
        index (uSize k) hi.val lo ≠ m) ∧
      (∀ hi : Fin (uSize k),
        hi.val ∈ summary.toFinset ↔ (clusters hi).toFinset.Nonempty) ∧
      WellFormed summary ∧
      ∀ hi, WellFormed (clusters hi)
```

- [x] **Step 2: Add named projections**

Provide documented theorems for node minimum correctness, maximum correctness,
detachment, summary membership, summary well-formedness, and cluster
well-formedness.  Each theorem must be a direct projection from `WellFormed` so
later delete branches do not destruct a six-way conjunction repeatedly.

- [x] **Step 3: Prove `empty_wellFormed`**

Use induction on `k`, `toFinset_empty`, and the recursive induction hypothesis:

```lean
theorem empty_wellFormed (k : Nat) : WellFormed (empty k) := by
  induction k with
  | zero => simp [WellFormed, MinCorrect, MaxCorrect, empty, toFinset]
  | succ k ih =>
      simp [WellFormed, MinCorrect, MaxCorrect, empty, toFinset_empty, ih]
```

- [x] **Step 4: Re-run the narrow build**

Expected: invariant declarations compile; only the old deletion theorem still
contains placeholders.

### Task 4: Prove bundled deletion correctness

**Files:**

- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean:868-end`

- [x] **Step 1: Replace the old theorem statement**

Introduce the bundled truth source:

```lean
theorem delete_correct {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) :
    WellFormed (delete x v) ∧
      (delete x v).toFinset = v.toFinset.erase x := by
```

Start with `Nat.strong_induction_on k` so both summary and cluster recursive
calls receive the bundled induction hypothesis.

- [x] **Step 2: Close the leaf branch**

Split `x = 0`, `x = 1`, and the outside-universe case.  Simplify `delete`,
`toFinset`, `MinCorrect`, `MaxCorrect`, and `WellFormed`; finish Boolean and
finite-set membership cases by extensionality.

- [x] **Step 3: Close empty and singleton node branches**

Use `MinCorrect.none_iff` to turn `mn = none` into `toFinset = ∅`; use extrema
bounds plus detached minimum to show `mn = mx = some m` represents exactly
`{m}`.  Prove both the unchanged and erase-singleton branches, including
well-formedness of the recursively empty result.

- [x] **Step 4: Close delete-minimum**

From summary minimum correctness and summary membership exactness, obtain the
first nonempty cluster.  From the cluster minimum correctness obtain its offset
membership.  Apply the bundled induction hypothesis to that cluster; if it
becomes empty, also apply the bundled induction hypothesis to the summary.
Re-establish whole-set extrema, detached minimum, exact summary membership, and
all recursive well-formedness fields.  Rewrite the represented set with the two
induction equalities and `index_high_low`/`high_index`/`low_index`.

- [x] **Step 5: Close ordinary cluster deletion**

Use the high/low index decomposition already proved in the file.  Apply the
bundled cluster induction hypothesis.  Split on whether the updated cluster is
empty; in the empty case, delete its high index from the summary using the
bundled summary induction hypothesis.  Repair the cached maximum only when the
erased key was the old maximum.  Prove unchanged clusters through
`Function.update_of_ne` and the changed cluster through `Function.update_self`.

- [x] **Step 6: Add projection theorems**

```lean
theorem delete_wellFormed (v) (x) (hwf : WellFormed v) :
    WellFormed (delete x v) := (delete_correct v x hwf).1

theorem delete_toFinset (v) (x) (hwf : WellFormed v) :
    (delete x v).toFinset = v.toFinset.erase x :=
  (delete_correct v x hwf).2
```

- [x] **Step 7: Run the red interface test again**

Run `lake env lean Tests/Chapter_20_Interface.lean`.

Expected: all new names resolve and the test exits successfully.

- [x] **Step 8: Prove axiom cleanliness**

Create a temporary check command that imports the section and runs:

```lean
#print axioms CLRS.Chapter20.VEBTreeMM.delete_correct
```

Expected: only standard Lean/Mathlib axioms, with no `sorryAx`.

### Task 5: Synchronize reader-facing status

**Files:**

- Modify: `CLRSLean/Chapter_20.lean:167-200`
- Modify: `docs/proof-map.md:2370-2405`
- Modify: `docs/clrs-proof-progress.csv:21`
- Modify: `CLRSLean/Progress.lean` when generated output changes

- [x] **Step 1: Update the chapter guide**

List `VEBTreeMM.WellFormed`, `empty_wellFormed`, `delete_correct`,
`delete_wellFormed`, and `delete_toFinset` as main Section 20.3 results.  State
that successor/predecessor correctness and control-flow-faithful cost semantics
remain partial.

- [x] **Step 2: Update the proof map and CSV prose**

Remove recursive deletion correctness from the gap, retain the two explicit
remaining targets, and describe deletion as correct for well-formed recursive
trees.  Set Chapter 20 `tracked_key_theorems` and
`proved_tracked_theorems` to 153, adding one tracked group for the bundled
recursive deletion theorem.

- [x] **Step 3: Regenerate the progress dashboard**

Run:

```bash
python3 scripts/check_progress_csv.py --write-dashboard
```

Expected: the CSV validates and `CLRSLean/Progress.lean` reflects any count or
description change.

### Task 6: Run completion gates and commit

**Files:** all modified files above.

- [x] **Step 1: Reject unfinished proof markers**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
```

Expected: no executable unfinished marker in the scoped files.

- [x] **Step 2: Run the narrow and repository checks**

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
python3 scripts/check_repository.py
git diff --check
```

Expected: every command exits zero.

- [x] **Step 3: Run full Lean and website builds**

```bash
lake build CLRSLean
lake build :literateHtml
```

Expected: both builds exit zero; pre-existing documentation warnings may remain
but there are no errors or placeholder-policy failures.

- [x] **Step 4: Review the final diff and commit**

```bash
git diff --stat main...HEAD
git diff main...HEAD -- \
  CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean \
  Tests/Chapter_20_Interface.lean CLRSLean/Chapter_20.lean \
  docs/proof-map.md docs/clrs-proof-progress.csv CLRSLean/Progress.lean
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean \
  Tests/Chapter_20_Interface.lean CLRSLean/Chapter_20.lean \
  docs/proof-map.md docs/clrs-proof-progress.csv CLRSLean/Progress.lean \
  docs/superpowers/plans/2026-07-14-ch20-veb-delete-correctness-plan.md
git commit -m "feat(ch20.3): prove recursive vEB deletion correctness"
```
