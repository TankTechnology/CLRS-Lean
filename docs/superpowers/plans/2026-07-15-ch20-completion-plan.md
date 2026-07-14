# Chapter 20 Recursive van Emde Boas Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the recursive `VEBTreeMM` operation set with invariant-preserving finite-set refinement, control-flow-aware costs, `O(log log u)` theorems, synchronized Chapter 20 status, evidence-based GitHub issue updates, and a clean fast-forward of remote `main`.

**Architecture:** Keep the existing three-module Chapter 20 layout and extend `Section_20_3_Recursive_VEB.lean` in proof layers: insertion, successor, predecessor, then costs. `WellFormed` remains the representation invariant; strong bundled semantic theorems are truth sources and public wrappers are projections. Cost definitions mirror executable branch predicates, while finite sets remain specifications rather than replacement implementations.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib, Lake, Finset/Option specifications, Git/GitHub CLI, Verso literate HTML.

---

## File map

- Modify `Tests/Chapter_20_Interface.lean`: test-first public theorem and cost surface.
- Create `Tests/Chapter_20_Axioms.lean`: persistent axiom audit for the headline Chapter 20 theorems.
- Modify `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`: insertion fix, operation proofs, cost evaluators, and asymptotic bounds.
- Modify `CLRSLean/Chapter_20.lean`: chapter status and headline theorem list.
- Modify `CLRSLean/Status.lean`: remove the obsolete recursive-operation gap while retaining concrete-memory refinement wording.
- Modify `docs/clrs-proof-progress.csv`: exact Chapter 20 status, theorem count, proved surface, and remaining refinement.
- Modify `docs/proof-map.md`: public theorem ledger and completion boundary.
- Modify `docs/chapters/chapter-20.md`: replace stale “recursive structure open” prose with the completed recursive operation matrix.
- Read/verify `literate.toml`: no module move is planned, so only ordering/title consistency is checked.
- Update GitHub issues #12, #42, and #50 after gathering the evidence named below.

### Task 1: Establish truthful issue and build baselines

**Files:**
- Read: `docs/superpowers/specs/2026-07-15-ch20-completion-design.md`
- Read: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`
- Read: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Confirm the isolated branch and clean worktree**

Run:

```bash
git status --short --branch
git rev-parse --abbrev-ref HEAD
git rev-parse HEAD
git rev-parse origin/main
```

Expected: branch `codex/ch20-complete`, no uncommitted files, and the branch contains the approved design commits on top of `origin/main`.

- [ ] **Step 2: Run the repository and Chapter 20 baselines**

Run:

```bash
python3 scripts/check_repository.py
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
git diff --check
```

Expected: all build/check commands exit zero and the placeholder search prints no matches. If dependency initialization is required, let `lake` finish before interpreting the baseline.

- [ ] **Step 3: Reopen the two prematurely closed issues with a respectful audit note**

Run:

```bash
gh issue reopen 12 --repo TankTechnology/CLRS-Lean
gh issue comment 12 --repo TankTechnology/CLRS-Lean --body 'Thank you for the substantial recursive vEB foundation already delivered here. A current-main audit found that the issue acceptance matrix is not yet fully satisfied: VEBTreeMM insertion invariant/refinement, recursive successor/predecessor correctness, and control-flow-aware costs for the complete operation set are still absent. I am reopening the epic while completing those named items on codex/ch20-complete; existing member, tower-depth, and deletion-correctness results remain intact.'
gh issue reopen 42 --repo TankTechnology/CLRS-Lean
gh issue comment 42 --repo TankTechnology/CLRS-Lean --body 'Thank you for introducing VEBTreeMM and the cached min/max algorithms. A current-main audit found that the issue was closed before its stated correctness and cost acceptance items were all kernel-checked: recursive successor/predecessor specifications, insertion invariant/refinement, and branch-faithful O(log log u) costs remain. I am reopening it only to finish those original deliverables; no completed work is being discarded.'
```

Expected: #12 and #42 report `OPEN`; each contains the exact audit comment above. Leave #50 open.

### Task 2: Define the insertion public contract first

**Files:**
- Modify: `Tests/Chapter_20_Interface.lean:160-175`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add the missing insertion interface checks**

Insert immediately before the existing deletion checks:

```lean
#check CLRS.Chapter20.VEBTreeMM.minimum_correct
#check CLRS.Chapter20.VEBTreeMM.maximum_correct
#check CLRS.Chapter20.VEBTreeMM.singleton_toFinset
#check CLRS.Chapter20.VEBTreeMM.singleton_wellFormed
#check CLRS.Chapter20.VEBTreeMM.insert_correct
#check CLRS.Chapter20.VEBTreeMM.insert_wellFormed
#check CLRS.Chapter20.VEBTreeMM.insert_toFinset
#check CLRS.Chapter20.VEBTreeMM.member_insert_iff
#check CLRS.Chapter20.VEBTreeMM.member_insert_self
#check CLRS.Chapter20.VEBTreeMM.member_insert_old
#check CLRS.Chapter20.VEBTreeMM.delete_member_iff
#check CLRS.Chapter20.VEBTreeMM.delete_member_deleted_false
#check CLRS.Chapter20.VEBTreeMM.delete_member_of_ne
```

- [ ] **Step 2: Run the interface and observe the red failure**

Run:

```bash
lake env lean Tests/Chapter_20_Interface.lean
```

Expected: failure begins with unknown
`CLRS.Chapter20.VEBTreeMM.minimum_correct`; it must not be a syntax or import
failure.

- [ ] **Step 3: Commit the red interface**

Run:

```bash
git add Tests/Chapter_20_Interface.lean
git commit -m 'test(ch20.3): require recursive insertion correctness'
```

### Task 3: Repair duplicate-minimum insertion and prove singleton facts

**Files:**
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean:525-632`
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean:1048-1072`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add the idempotent cached-minimum guard**

Replace the `some m` node branch of `VEBTreeMM.insert` with the same existing body guarded as follows:

```lean
      | some m =>
          if h_same : x = m then
            VEBTreeMM.node mn mx summary clusters
          else
            let x' := if x < m then m else x
            let mn' := if x < m then some x else mn
            let mx' := match mx with
              | none => some x
              | some v => if x > v then some x else mx
            if h : high (uSize k0) x' < uSize k0 then
              let hi : Fin (uSize k0) := ⟨high (uSize k0) x', h⟩
              let lo := low (uSize k0) x'
              have h_lo : lo < uSize k0 := low_lt (uSize_pos k0)
              if (clusters hi).minimum = none then
                VEBTreeMM.node mn' mx' (insert (high (uSize k0) x') summary)
                  (Function.update clusters hi (singleton k0 lo h_lo))
              else
                VEBTreeMM.node mn' mx' summary
                  (Function.update clusters hi (insert lo (clusters hi)))
            else
              VEBTreeMM.node mn' mx' summary clusters
```

This is the only behavioral change: a duplicate of the detached minimum is a no-op. Leaf insertion remains idempotent through its Boolean bits.

- [ ] **Step 2: Expose cached-extrema correctness and prove exact singleton semantics**

First add the two top-level cached-extrema wrappers:

```lean
/-- The cached minimum exactly describes the least represented key. -/
theorem minimum_correct {k : Nat} {v : VEBTreeMM k} (hwf : WellFormed v) :
    MinCorrect v.minimum v.toFinset :=
  hwf.minCorrect

/-- The cached maximum exactly describes the greatest represented key. -/
theorem maximum_correct {k : Nat} {v : VEBTreeMM k} (hwf : WellFormed v) :
    MaxCorrect v.maximum v.toFinset :=
  hwf.maxCorrect
```

Then prove exact singleton semantics.

Add after `empty_wellFormed`:

```lean
/-- A bounded singleton tree represents exactly its supplied key. -/
theorem singleton_toFinset (k : Nat) (x : Nat) (hx : x < uSize k) :
    (singleton k x hx).toFinset = {x} := by
  cases k with
  | zero =>
      rw [uSize_zero] at hx
      by_cases hx0 : x = 0
      · subst x
        simp [singleton, toFinset]
      · have hx1 : x = 1 := by omega
        subst x
        simp [singleton, toFinset]
  | succ k =>
      simp [singleton, toFinset, toFinset_empty, hx]
```

Run the narrow source build. If the final `simp` leaves a `Function`-indexed empty-cluster goal, discharge it with `funext` followed by `simp [toFinset_empty]`, without changing the theorem statement.

- [ ] **Step 3: Prove singleton well-formedness**

Add immediately after `singleton_toFinset`:

```lean
/-- A bounded singleton tree satisfies the recursive cached-extrema invariant. -/
theorem singleton_wellFormed (k : Nat) (x : Nat) (hx : x < uSize k) :
    WellFormed (singleton k x hx) := by
  cases k with
  | zero =>
      rw [uSize_zero] at hx
      by_cases hx0 : x = 0
      · subst x
        simp [singleton, WellFormed, MinCorrect, MaxCorrect, toFinset]
      · have hx1 : x = 1 := by omega
        subst x
        simp [singleton, WellFormed, MinCorrect, MaxCorrect, toFinset]
  | succ k =>
      simp [singleton, WellFormed, MinCorrect, MaxCorrect,
        singleton_toFinset, empty_wellFormed, toFinset_empty, hx]
```

- [ ] **Step 4: Verify the two singleton checks turn green while insertion remains red**

Run:

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
```

Expected: source build succeeds; interface now fails first at `insert_correct`.

- [ ] **Step 5: Commit the algorithm fix and singleton layer**

Run:

```bash
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean
git commit -m 'fix(ch20.3): preserve detached minimum on duplicate insert'
```

### Task 4: Prove recursive insertion invariant and Finset refinement

**Files:**
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean` after the deletion helper block and before `delete_correct`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add insertion-normalization helpers**

Add named lemmas with these exact contracts:

```lean
theorem toFinset_update_cluster_insert {k : Nat}
    (mn mx : Option Nat) (summary : VEBTreeMM k)
    (clusters : Fin (uSize k) → VEBTreeMM k)
    (hi : Fin (uSize k)) (cluster' : VEBTreeMM k) (x : Nat)
    (hcluster : cluster'.toFinset = Finset.insert x (clusters hi).toFinset) :
    (VEBTreeMM.node mn mx summary
      (Function.update clusters hi cluster')).toFinset =
      Finset.insert (index (uSize k) hi.val x)
        (VEBTreeMM.node mn mx summary clusters).toFinset := by
  ext y
  rw [mem_toFinset_node_update_cluster, mem_toFinset_node]
  simp only [Finset.mem_insert, hcluster]
  constructor
  · rintro (hmin | hnew | hold)
    · exact Or.inr (Or.inl hmin)
    · rcases hnew with ⟨lo, hlo, rfl⟩
      rcases hlo with (rfl | hlo)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨hi, lo, hlo, rfl⟩)
    · exact Or.inr (Or.inr hold)
  · rintro (rfl | hrest)
    · exact Or.inr ⟨x, Finset.mem_insert_self x _, rfl⟩
    · rcases hrest with (hmin | hclusterOld)
      · exact Or.inl hmin
      · rcases hclusterOld with ⟨j, lo, hlo, rfl⟩
        by_cases hji : j = hi
        · subst j
          exact Or.inr ⟨lo, Finset.mem_insert_of_mem hlo, rfl⟩
        · exact Or.inr (Or.inr ⟨j, hji, lo, hlo, rfl⟩)
```

If `simp only` exposes the stored-minimum disjunction in a different association, normalize with the already proved `mem_toFinset_node_update_cluster` theorem rather than unfolding `Finset.biUnion`.

Add two summary-update helpers, one for an empty cluster becoming `singleton` and one for a nonempty cluster remaining represented in the unchanged summary. State each as the exact `hi ∈ summary.toFinset ↔ cluster.Nonempty` condition required by `WellFormed`.

- [ ] **Step 2: Prove the bundled insertion theorem by strong induction**

Use this exact public statement:

```lean
/-- Recursive lazy-min insertion preserves `WellFormed` and refines `Finset.insert`. -/
theorem insert_correct : ∀ {k : Nat} (v : VEBTreeMM k) (x : Nat),
    WellFormed v → x < uSize k →
      WellFormed (insert x v) ∧
        (insert x v).toFinset = Finset.insert x v.toFinset
```

The proof program is exact:

1. `intro k` and perform `Nat.strong_induction_on k`.
2. In the leaf case, rewrite `uSize_zero`, use `interval_cases x`, enumerate
   the cached options and bits, and close with `simp` over `insert`,
   `WellFormed`, `MinCorrect`, `MaxCorrect`, and `toFinset`.
3. In the node/`mn = none` case, obtain whole-set emptiness from
   `hwf.minimum_none_iff`; use `node_summary_mem_iff` and recursively well-formed
   empty clusters to show the retained summary and clusters are empty; assemble
   the singleton result using `singleton_wellFormed`.
4. In the node/`mn = some m` case, first split `x = m`, which is the new no-op
   branch. Then split `x < m`, the high bound, and cluster emptiness in the same
   order as `insert`.
5. Apply `ih k0 (Nat.lt_succ_self k0)` to exactly the selected summary or
   cluster. In the min-swap branch, prove the new detached minimum using
   `x < m` and `hwf.minimum_le`; otherwise preserve the old detached minimum
   using `m < x`.
6. Assemble all six node fields of `WellFormed`, then prove the Finset equation
   with `toFinset_update_cluster_insert` and the summary-update helpers.

Do not add a nonmembership hypothesis and do not rebuild the result from a
Finset.

- [ ] **Step 3: Add projection wrappers**

```lean
/-- Recursive insertion preserves the min/max-augmented vEB invariant. -/
theorem insert_wellFormed {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    WellFormed (insert x v) :=
  (insert_correct v x hwf hx).1

/-- Recursive insertion refines finite-set insertion. -/
theorem insert_toFinset {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    (insert x v).toFinset = Finset.insert x v.toFinset :=
  (insert_correct v x hwf hx).2
```

Add the insertion membership family by composing `member_correct` with
`insert_toFinset`:

```lean
theorem member_insert_iff {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    member y (insert x v) = true ↔ y = x ∨ member y v = true := by
  rw [member_correct (insert x v) y, insert_toFinset v x hwf hx,
    Finset.mem_insert, ← member_correct v y]

theorem member_insert_self {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    member x (insert x v) = true :=
  (member_insert_iff v x x hwf hx).2 (Or.inl rfl)

theorem member_insert_old {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) (hx : x < uSize k)
    (hy : member y v = true) :
    member y (insert x v) = true :=
  (member_insert_iff v x y hwf hx).2 (Or.inr hy)
```

Add the deletion membership family from the already proved `delete_toFinset`:

```lean
theorem delete_member_iff {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) :
    member y (delete x v) = true ↔ y ≠ x ∧ member y v = true := by
  rw [member_correct (delete x v) y, delete_toFinset v x hwf,
    Finset.mem_erase, ← member_correct v y]

theorem delete_member_deleted_false {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) :
    member x (delete x v) = false := by
  apply Bool.eq_false_iff.mpr
  intro hmem
  exact (delete_member_iff v x x hwf).1 hmem |>.1 rfl

theorem delete_member_of_ne {k : Nat} (v : VEBTreeMM k) (x y : Nat)
    (hwf : WellFormed v) (hyx : y ≠ x) (hy : member y v = true) :
    member y (delete x v) = true :=
  (delete_member_iff v x y hwf).2 ⟨hyx, hy⟩
```

- [ ] **Step 4: Run the insertion green gate**

Run:

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean Tests/Chapter_20_Interface.lean
git diff --check
```

Expected: all commands exit zero; placeholder search prints no matches.

- [ ] **Step 5: Commit insertion correctness**

```bash
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean Tests/Chapter_20_Interface.lean
git commit -m 'feat(ch20.3): prove recursive vEB insertion correctness'
```

### Task 5: Define and prove the successor public surface

**Files:**
- Modify: `Tests/Chapter_20_Interface.lean`
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add successor checks and observe red**

Add:

```lean
#check CLRS.Chapter20.VEBTreeMM.SuccessorSpec
#check CLRS.Chapter20.VEBTreeMM.successor_spec
#check CLRS.Chapter20.VEBTreeMM.successor_correct
#check CLRS.Chapter20.VEBTreeMM.successor_mem
#check CLRS.Chapter20.VEBTreeMM.successor_gt
#check CLRS.Chapter20.VEBTreeMM.successor_le
#check CLRS.Chapter20.VEBTreeMM.successor_lt_uSize
#check CLRS.Chapter20.VEBTreeMM.successor_none_iff
#check CLRS.Chapter20.VEBTreeMM.successor_none_of_no_gt
#check CLRS.Chapter20.VEBTreeMM.successor_ne_none_of_exists_gt
```

Run `lake env lean Tests/Chapter_20_Interface.lean` and confirm an unknown `SuccessorSpec` failure, then commit:

```bash
git add Tests/Chapter_20_Interface.lean
git commit -m 'test(ch20.3): require recursive successor specification'
```

- [ ] **Step 2: Add the bundled Option result predicate**

```lean
def SuccessorSpec (s : Finset Nat) (x : Nat) : Option Nat → Prop
  | none => ∀ y, y ∈ s → ¬ x < y
  | some y =>
      y ∈ s ∧ x < y ∧ ∀ z, z ∈ s → x < z → y ≤ z
```

Add strict same-cluster ordering and high/low recovery helpers:

```lean
theorem index_lt_index_of_low_lt {m hi lo₁ lo₂ : Nat} (hlo : lo₁ < lo₂) :
    index m hi lo₁ < index m hi lo₂ := by
  simpa [index] using Nat.add_lt_add_left hlo (m * hi)

theorem high_eq_of_index_eq {m x hi lo : Nat} (hm : 0 < m) (hlo : lo < m)
    (hidx : index m hi lo = x) : high m x = hi := by
  rw [← hidx, high_index hlo]

theorem low_eq_of_index_eq {m x hi lo : Nat} (hlo : lo < m)
    (hidx : index m hi lo = x) : low m x = lo := by
  rw [← hidx, low_index hlo]
```

- [ ] **Step 3: Prove `successor_spec` by strong induction**

Use this exact truth-source statement:

```lean
theorem successor_spec : ∀ {k : Nat} (v : VEBTreeMM k) (x : Nat),
    WellFormed v → SuccessorSpec v.toFinset x (successor x v)
```

Prove it by strong induction on `k`. Enumerate the leaf bits and simplify with
`SuccessorSpec`. At a node, split `mn`, the cached-minimum shortcut, the high
bound, `cluster.maximum`, the same-cluster comparison, and recursive Option
results in exactly the executable order. For a same-cluster result, apply the cluster induction hypothesis and
`index_lt_index_of_low_lt`/`index_le_index_of_low_le`. For a summary result,
apply the summary induction hypothesis, convert summary membership with
`node_summary_mem_iff`, obtain the selected cluster minimum from
`node_cluster.minimum_mem`, and order later clusters with
`index_lt_index_of_high_lt`. For a recursive `none`, use the `none` branch of
`SuccessorSpec` to refute every represented candidate. These four conversions
must be named local `have` facts before arithmetic normalization.

- [ ] **Step 4: Add successor projections**

Implement the declarations checked by the interface. `successor_correct` is the
`some` reduction of `successor_spec`; `successor_none_iff` uses the `none`
reduction in one direction and Option case analysis plus `successor_correct` in
the other. Every remaining theorem is a direct projection, matching the
Section 20.2 signatures with `WellFormed v` replacing `Represents t s`.

- [ ] **Step 5: Verify and commit successor correctness**

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
git diff --check
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean Tests/Chapter_20_Interface.lean
git commit -m 'feat(ch20.3): prove recursive vEB successor correctness'
```

### Task 6: Define and prove the predecessor public surface

**Files:**
- Modify: `Tests/Chapter_20_Interface.lean`
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add predecessor checks and observe red**

```lean
#check CLRS.Chapter20.VEBTreeMM.PredecessorSpec
#check CLRS.Chapter20.VEBTreeMM.predecessor_spec
#check CLRS.Chapter20.VEBTreeMM.predecessor_correct
#check CLRS.Chapter20.VEBTreeMM.predecessor_mem
#check CLRS.Chapter20.VEBTreeMM.predecessor_lt
#check CLRS.Chapter20.VEBTreeMM.le_predecessor
#check CLRS.Chapter20.VEBTreeMM.predecessor_lt_uSize
#check CLRS.Chapter20.VEBTreeMM.predecessor_none_iff
#check CLRS.Chapter20.VEBTreeMM.predecessor_none_of_no_lt
#check CLRS.Chapter20.VEBTreeMM.predecessor_ne_none_of_exists_lt
```

Run the interface, confirm unknown `PredecessorSpec`, and commit the red test.

- [ ] **Step 2: Add the symmetric bundled predicate and strong proof**

```lean
def PredecessorSpec (s : Finset Nat) (x : Nat) : Option Nat → Prop
  | none => ∀ y, y ∈ s → ¬ y < x
  | some y =>
      y ∈ s ∧ y < x ∧ ∀ z, z ∈ s → z < x → z ≤ y

theorem predecessor_spec : ∀ {k : Nat} (v : VEBTreeMM k) (x : Nat),
    WellFormed v → PredecessorSpec v.toFinset x (predecessor x v)
```

Prove it by the same strong-induction structure, but split `mx` and the
cached-maximum shortcut first. Use `index_lt_index_of_high_lt` with reversed cluster roles for earlier
clusters, and the strict/weak same-cluster offset lemmas for reconstructed
keys. The out-of-universe branch still queries the summary and must be covered,
not simplified away.

- [ ] **Step 3: Add all predecessor projections**

Implement the ten checked declarations. Follow the same truth-source pattern as
successor and the exact public naming in Section 20.2.

- [ ] **Step 4: Verify and commit predecessor correctness**

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
git diff --check
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean Tests/Chapter_20_Interface.lean
git commit -m 'feat(ch20.3): prove recursive vEB predecessor correctness'
```

### Task 7: Add cost interfaces for all seven operations

**Files:**
- Modify: `Tests/Chapter_20_Interface.lean`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add new cost/result checks**

```lean
#check CLRS.Chapter20.VEBTreeMM.memberWithCost
#check CLRS.Chapter20.VEBTreeMM.memberWithCost_result
#check CLRS.Chapter20.VEBTreeMM.memberCost_le
#check CLRS.Chapter20.VEBTreeMM.minimumWithCost
#check CLRS.Chapter20.VEBTreeMM.minimumWithCost_result
#check CLRS.Chapter20.VEBTreeMM.minimumCost_eq_one
#check CLRS.Chapter20.VEBTreeMM.maximumWithCost
#check CLRS.Chapter20.VEBTreeMM.maximumWithCost_result
#check CLRS.Chapter20.VEBTreeMM.maximumCost_eq_one
#check CLRS.Chapter20.VEBTreeMM.insertWithCost
#check CLRS.Chapter20.VEBTreeMM.insertWithCost_result
#check CLRS.Chapter20.VEBTreeMM.insertCost_le
#check CLRS.Chapter20.VEBTreeMM.successorWithCost
#check CLRS.Chapter20.VEBTreeMM.successorWithCost_result
#check CLRS.Chapter20.VEBTreeMM.successorCost_le
#check CLRS.Chapter20.VEBTreeMM.predecessorWithCost
#check CLRS.Chapter20.VEBTreeMM.predecessorWithCost_result
#check CLRS.Chapter20.VEBTreeMM.predecessorCost_le
#check CLRS.Chapter20.VEBTreeMM.deleteWithCost
#check CLRS.Chapter20.VEBTreeMM.deleteWithCost_result
#check CLRS.Chapter20.VEBTreeMM.deleteCost_le
#check CLRS.Chapter20.VEBTreeMM.deleteDepth
#check CLRS.Chapter20.VEBTreeMM.deleteDepth_le
#check CLRS.Chapter20.VEBTreeMM.veb_all_operations_bigO_loglog_u
```

- [ ] **Step 2: Verify red and commit**

Run the interface and confirm unknown `memberWithCost`, then commit:

```bash
git add Tests/Chapter_20_Interface.lean
git commit -m 'test(ch20.3): require faithful costs for all vEB operations'
```

### Task 8: Implement member, extrema, insert, successor, and predecessor costs

**Files:**
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean:530-766`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Add cached-extrema and member costs**

Use these definitions:

```lean
def memberCost : {k : Nat} → Nat → VEBTreeMM k → Nat
  | _, _, .leaf _ _ _ _ => 1
  | _, x, @VEBTreeMM.node k0 mn _ _ clusters =>
      if mn = some x then 1
      else if h : high (uSize k0) x < uSize k0 then
        1 + memberCost (low (uSize k0) x)
          (clusters ⟨high (uSize k0) x, h⟩)
      else 1

def memberWithCost {k : Nat} (x : Nat) (v : VEBTreeMM k) : Bool × Nat :=
  (member x v, memberCost x v)

theorem memberWithCost_result {k : Nat} (x : Nat) (v : VEBTreeMM k) :
    (memberWithCost x v).1 = member x v := rfl

def minimumWithCost {k : Nat} (v : VEBTreeMM k) : Option Nat × Nat :=
  (minimum v, 1)

def maximumWithCost {k : Nat} (v : VEBTreeMM k) : Option Nat × Nat :=
  (maximum v, 1)
```

Add the `rfl` result theorems and `minimumCost_eq_one` /
`maximumCost_eq_one` as equalities on the second projections.

- [ ] **Step 2: Define branch-faithful insert cost**

Mirror the guarded `insert` branches. Return one for leaves, empty nodes,
duplicate minima, and failed high bounds. In the empty-cluster branch return
`1 + insertCost hi summary`; in the nonempty-cluster branch return
`1 + insertCost lo (clusters hi)`. Define `insertWithCost` as the pair of
`insert` and this cost, so `insertWithCost_result` is `rfl`.

- [ ] **Step 3: Replace the dummy successor and predecessor costs**

For `successorCost`, mirror `successor` through the cached-min shortcut,
high-bound check, cluster maximum, and same-cluster comparison. Charge
`1 + successorCost lo cluster` only in the same-cluster recursive branch;
otherwise charge `1 + successorCost hi summary` exactly when the executable
successor queries the summary. Return one for terminal branches.

For `predecessorCost`, mirror all predecessor branches, including the
out-of-universe summary query. Define both `*WithCost` pairs and their `rfl`
result theorems.

- [ ] **Step 4: Prove the recursive nondelete bounds**

Prove by structural induction on `v`:

```lean
theorem memberCost_le {k : Nat} (v : VEBTreeMM k) (x : Nat) :
    memberCost x v ≤ k + 1

theorem insertCost_le {k : Nat} (v : VEBTreeMM k) (x : Nat) :
    insertCost x v ≤ k + 1

theorem successorCost_le {k : Nat} (v : VEBTreeMM k) (x : Nat) :
    successorCost x v ≤ k + 1

theorem predecessorCost_le {k : Nat} (v : VEBTreeMM k) (x : Nat) :
    predecessorCost x v ≤ k + 1
```

At a node, unfold only the selected cost, split its branch predicates, apply
the summary or indexed-cluster induction hypothesis, and close arithmetic with
`omega`. No `WellFormed` premise is needed because every recursive argument has
universe level `k0` regardless of branch.

- [ ] **Step 5: Verify and commit the first cost layer**

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
git diff --check
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean
git commit -m 'feat(ch20.3): add faithful member insert and neighbor costs'
```

Expected: source builds; interface remains red only on delete/new headline cost names.

### Task 9: Implement and prove actual delete work and depth costs

**Files:**
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean:767-872` and after `delete_correct`
- Test: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Replace the dummy delete cost with actual branch work**

Define `deleteCost` to return one on a leaf or terminal node branch. In each
recursive cluster branch, compute the same `cluster' := delete lo cluster` as
`delete`. Charge `1 + deleteCost lo cluster`; when `cluster'.minimum.isNone`,
also add `deleteCost hi summary` because the executable algorithm performs that
second call. Mirror both the delete-minimum promotion branch and the ordinary
cluster branch.

Define `deleteDepth` with the same branch predicates. For an empty-cluster
branch use:

```lean
1 + max (deleteDepth lo cluster) (deleteDepth hi summary)
```

and for a nonempty-cluster branch use `1 + deleteDepth lo cluster`. Define:

```lean
def deleteWithCost {k : Nat} (x : Nat) (v : VEBTreeMM k) : VEBTreeMM k × Nat :=
  (delete x v, deleteCost x v)

theorem deleteWithCost_result {k : Nat} (x : Nat) (v : VEBTreeMM k) :
    (deleteWithCost x v).1 = delete x v := rfl
```

- [ ] **Step 2: Prove the empty-or-singleton constant-cost lemma**

Use this exact helper statement:

```lean
theorem deleteCost_eq_one_of_subsingleton {k : Nat}
    (v : VEBTreeMM k) (x : Nat) (hwf : WellFormed v)
    (hsub : v.toFinset ⊆ {x}) :
    deleteCost x v = 1
```

Prove it by cases on whether `v.toFinset` is empty. In the empty case,
`minimum_none_iff` makes the node branch terminal. In the nonempty case, choose
a member `y`; `hsub` gives `y = x`, while `minimum_mem`, `maximum_mem`, and the
minimum/maximum bounds force both caches to `some x`. A leaf costs one by
definition; a node then takes its equal-extrema terminal branch.

- [ ] **Step 3: Prove an emptied deletion input is subsingleton**

Add a private helper:

```lean
theorem toFinset_subset_singleton_of_erase_eq_empty {k : Nat}
    (v : VEBTreeMM k) (x : Nat)
    (hempty : v.toFinset.erase x = ∅) :
    v.toFinset ⊆ {x} := by
  intro y hy
  by_cases hyx : y = x
  · simpa [hyx]
  · have hmem : y ∈ v.toFinset.erase x :=
      Finset.mem_erase.mpr ⟨hyx, hy⟩
    exfalso
    simpa [hempty] using hmem
```

- [ ] **Step 4: Prove delete work and depth bounds**

Use strong induction on `k` and the same cases as `delete_correct`:

```lean
theorem deleteCost_le {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) :
    deleteCost x v ≤ 2 * k + 1

theorem deleteDepth_le {k : Nat} (v : VEBTreeMM k) (x : Nat) :
    deleteDepth x v ≤ k + 1
```

In an empty-cluster branch, use `delete_correct` to rewrite the child result,
`minimum_none_iff` to obtain erased-set emptiness, the helper from Step 3 to
obtain a subset of the deleted singleton, and
`deleteCost_eq_one_of_subsingleton` for the first child call. The summary
induction hypothesis then gives
`1 + 1 + (2 * k0 + 1) = 2 * (k0 + 1) + 1`. For depth, apply both child
induction hypotheses and `Nat.max_le`; no semantic premise is required.

- [ ] **Step 5: Verify and commit delete cost**

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
git diff --check
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean
git commit -m 'feat(ch20.3): prove control-flow-aware delete cost'
```

### Task 10: Package the all-operation asymptotic theorem

**Files:**
- Modify: `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`
- Modify: `Tests/Chapter_20_Interface.lean`

- [ ] **Step 1: Define worst-case tower-level bounds**

```lean
def standardOperationCostBound (k : Nat) : Nat := k + 1
def deleteCostBound (k : Nat) : Nat := 2 * k + 1
```

Add wrappers connecting each concrete cost to its bound. Minimum and maximum
use the constant function one; member, insert, successor, and predecessor use
`standardOperationCostBound`; delete uses `deleteCostBound` under `WellFormed`.

- [ ] **Step 2: Prove the bound functions are O(log log u)**

Reuse `VEBTree.loglog_uSize` and the existing Chapter 3 `isBigO_iff` proof
pattern:

```lean
theorem standardOperationCostBound_bigO_loglog_u :
    CLRS.Chapter03.isBigO
      (fun k => (standardOperationCostBound k : ℝ))
      (fun k => (Nat.log 2 (Nat.log 2 (uSize k)) : ℝ))

theorem deleteCostBound_bigO_loglog_u :
    CLRS.Chapter03.isBigO
      (fun k => (deleteCostBound k : ℝ))
      (fun k => (Nat.log 2 (Nat.log 2 (uSize k)) : ℝ))
```

For the delete bound choose a real constant at least `3` and use `nlinarith`
after rewriting `loglog_uSize`.

- [ ] **Step 3: Add the headline conjunction**

```lean
theorem veb_all_operations_bigO_loglog_u :
    CLRS.Chapter03.isBigO
        (fun k => (standardOperationCostBound k : ℝ))
        (fun k => (Nat.log 2 (Nat.log 2 (uSize k)) : ℝ)) ∧
      CLRS.Chapter03.isBigO
        (fun k => (deleteCostBound k : ℝ))
        (fun k => (Nat.log 2 (Nat.log 2 (uSize k)) : ℝ)) :=
  ⟨standardOperationCostBound_bigO_loglog_u,
    deleteCostBound_bigO_loglog_u⟩
```

Document that cached extrema are `O(1)` and hence no larger than the advertised
operation family; do not relabel their pointwise constant cost as a recursive
depth.

- [ ] **Step 4: Add and run the persistent axiom audit, then commit**

Create `Tests/Chapter_20_Axioms.lean` with:

```lean
import CLRSLean.Chapter_20

#print axioms CLRS.Chapter20.VEBTreeMM.insert_correct
#print axioms CLRS.Chapter20.VEBTreeMM.successor_correct
#print axioms CLRS.Chapter20.VEBTreeMM.predecessor_correct
#print axioms CLRS.Chapter20.VEBTreeMM.delete_correct
#print axioms CLRS.Chapter20.VEBTreeMM.veb_all_operations_bigO_loglog_u
```

Expected: no `sorryAx` and no project-defined axiom. Then run the source and
interface builds and commit:

```bash
lake env lean Tests/Chapter_20_Axioms.lean
git add CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean Tests/Chapter_20_Interface.lean Tests/Chapter_20_Axioms.lean
git commit -m 'feat(ch20.3): close recursive vEB operation bounds'
```

### Task 11: Synchronize Chapter 20 status and theorem ledgers

**Files:**
- Modify: `CLRSLean/Chapter_20.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/proof-map.md`
- Modify: `docs/chapters/chapter-20.md`
- Verify: `literate.toml`

- [ ] **Step 1: Update reader-facing Chapter 20 prose**

Change Section 20.3 from `partial` to `main-proof-complete-for-correctness`.
List the bundled insert/successor/predecessor/delete theorems and the headline
cost theorem. Replace “recursive operations remain” with this exact boundary:

```text
The recursive cached-min/max model now proves all seven vEB operations correct,
with constant cached extrema and control-flow-aware O(log log u) bounds for the
recursive operations. Concrete pointer/array allocation and hardware-level RAM
timing remain a separate implementation refinement.
```

- [ ] **Step 2: Update the progress CSV exactly**

In the Chapter 20 row:

- set status to `main-proof-complete-for-correctness`;
- preserve sections `20.1;20.2;20.3`;
- increase tracked/proved counts by the exact number of newly advertised public
  theorems;
- name insert invariant/refinement, recursive successor/predecessor strong
  specifications, control-flow cost bounds, and the all-operation asymptotic
  theorem in the proved-surface field;
- set the remaining-work field to concrete pointer/array storage and hardware
  RAM constants only.

Compute the exact progress increment from the newly advertised theorem list,
not from raw `#check` lines, because interface checks also include definitions
and previously proved declarations. Inspect theorem additions with:

```bash
git diff --unified=0 656f45b...HEAD -- CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean | rg '^\+theorem '
```

List every new headline theorem and useful public projection in the proved
surface, exclude private normalization helpers, and increase both tracked and
proved by exactly that listed count. Tracked and proved must remain equal.

- [ ] **Step 3: Update proof map, chapter guide, and global status**

Make the theorem names and completion boundary identical across all three
documents. Remove the stale statement in `docs/chapters/chapter-20.md` that the
recursive summary/cluster state is open. In `CLRSLean/Status.lean`, keep Chapter
20's concrete-memory refinement separate from Chapters 18-19 pointer/page gaps.

- [ ] **Step 4: Verify documentation and commit**

```bash
python3 scripts/check_progress_csv.py
python3 scripts/check_site_consistency.py
python3 scripts/check_repository.py
git diff --check
git add CLRSLean/Chapter_20.lean CLRSLean/Status.lean docs/clrs-proof-progress.csv docs/proof-map.md docs/chapters/chapter-20.md
git commit -m 'docs(ch20): record recursive vEB completion'
```

### Task 12: Run the full completion audit

**Files:**
- Verify: all files changed since `origin/main`

- [ ] **Step 1: Audit every approved requirement against source evidence**

Run:

```bash
git diff --stat origin/main...HEAD
git diff --name-only origin/main...HEAD
rg -n 'Current gaps|Current Gaps|Remaining Work|partial|future target|structural depth surrogate' CLRSLean/Chapter_20.lean CLRSLean/Chapter_20 docs/proof-map.md docs/chapters/chapter-20.md docs/clrs-proof-progress.csv
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
```

Expected: every approved code/doc file is present; no obsolete recursive-operation gap remains; no executable placeholder appears. Any remaining prose must refer only to the concrete-memory/hardware refinement boundary.

- [ ] **Step 2: Run the complete verification matrix**

```bash
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
lake env lean Tests/Chapter_20_Axioms.lean
python3 scripts/check_repository.py
lake build CLRSLean
lake build :literateHtml
git diff --check
git status --short --branch
```

Expected: every command exits zero; the final status is clean on
`codex/ch20-complete`. Existing nonfatal compiler warnings may be recorded but
must not be represented as new failures.

- [ ] **Step 3: Request code review**

Use the `superpowers:requesting-code-review` skill. Review against the approved
design and this plan, with particular attention to duplicate insertion,
summary fallback ordering, delete's two-call constant-factor accounting, and
status claims. Resolve every high/medium correctness finding and repeat the
full matrix after any change.

### Task 13: Integrate, update issues, and clean remote state

**Files:**
- No source edits unless final verification discovers a real defect.

- [ ] **Step 1: Fetch and prove fast-forward safety**

```bash
git fetch origin main
git rev-list --left-right --count codex/ch20-complete...origin/main
```

Expected: the feature branch is only ahead of `origin/main`; the right-hand
count is zero. If remote `main` advanced, rebase or merge only after auditing
the new commits and rerunning the full verification matrix.

- [ ] **Step 2: Fast-forward local and remote main without force**

```bash
git switch main
git merge --ff-only codex/ch20-complete
git push origin main
```

Expected: push reports a normal fast-forward. Never use `--force` or
`--force-with-lease` for this integration.

- [ ] **Step 3: Post evidence and close the three issues**

Use the pushed commit hash and exact theorem names in English comments:

```bash
commit=$(git rev-parse HEAD)
gh issue comment 42 --repo TankTechnology/CLRS-Lean --body "Completed on main at commit ${commit}. VEBTreeMM.insert_correct now proves lazy-min insertion preserves WellFormed and refines Finset.insert; successor_spec/successor_correct and predecessor_spec/predecessor_correct establish the recursive least-greater/greatest-less contracts; branch-faithful insert/successor/predecessor costs are bounded by k+1 and packaged through the Chapter 3 O(log log u) wrapper. Tests/Chapter_20_Interface.lean and the Chapter 20 ledgers expose the complete public surface, with no sorry/admit/axiom placeholders."
gh issue close 42 --repo TankTechnology/CLRS-Lean --reason completed

gh issue comment 50 --repo TankTechnology/CLRS-Lean --body "Completed on main at commit ${commit}. delete_correct preserves VEBTreeMM.WellFormed and exactly refines Finset.erase. The new deleteCost follows both actual recursive calls, proves a constant-factor linear tower-level work bound using the singleton-cluster lemma, while deleteDepth is at most k+1; deleteCostBound_bigO_loglog_u supplies the requested O(log log u) result. The distinction between actual work and recursive depth is recorded explicitly in source and docs."
gh issue close 50 --repo TankTechnology/CLRS-Lean --reason completed

gh issue comment 12 --repo TankTechnology/CLRS-Lean --body "Epic acceptance is complete on main at commit ${commit}: the tower-universe recursive VEBTreeMM implements and proves member, cached minimum/maximum, lazy-min insert, successor, predecessor, and delete against the finite-set specification. All recursive operations have control-flow-aware tower-level bounds and O(log log u) packaging; cached extrema are constant time. The Chapter 20 interface, proof map, progress CSV, status page, and literate site are synchronized. Concrete pointer/array allocation and hardware cycle timing remain explicitly outside this mathematical completion boundary."
gh issue close 12 --repo TankTechnology/CLRS-Lean --reason completed
```

- [ ] **Step 4: Verify remote state and remove only this feature branch if present**

```bash
git ls-remote origin refs/heads/main refs/heads/codex/ch20-complete
git rev-parse main
git status --short --branch
```

Expected: remote and local `main` hashes match. If
`refs/heads/codex/ch20-complete` exists because the feature branch was pushed,
remove only that branch with:

```bash
git push origin --delete codex/ch20-complete
```

Do not modify `ch13-rb-delete-exec`, PR #20, PR #85, or any contributor-owned
branch. Confirm #12, #42, and #50 are closed and their final comments contain
the pushed evidence.
