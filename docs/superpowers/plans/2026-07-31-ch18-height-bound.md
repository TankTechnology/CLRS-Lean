# Chapter 18 Structural Height Bound Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.  Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the Chapter 18 B-tree invariants imply the textbook
minimum-key and logarithmic-height bounds while preserving the legal empty-root
case.

**Architecture:** Add a focused Section 18.1 child module.  Count key slots with
`totalKeys`, prove an exact `totalKeys + 1` recurrence for internal nodes, use
non-root occupancy and same-depth induction to obtain a power lower bound, then
derive the root, `minKeys`, and `Nat.log` surfaces.

**Tech Stack:** Lean 4, Mathlib, Lake, the existing Chapter 18 `BTree` model,
chapter-local interface tests.

---

## File Map

- Create
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean`
  - owns `totalKeys`, counting helpers, the non-root induction, and all public
    root/minimum-key/logarithmic-height theorems;
  - imports only `CLRSLean.Chapter_18.Section_18_1_B_Tree_Model`.
- Create `Tests/Chapter_18_Height_Interface.lean`
  - freezes the seven public contracts;
  - checks empty, leaf, and height-one arithmetic boundaries.
- Modify `CLRSLean/Chapter_18.lean`
  - imports and lists the final Section 18.1 theorem family;
  - changes the chapter from `partial` to correctness-complete.
- Modify `literate.toml`
  - registers `HeightBound` as a child of the Section 18.1 model.
- Modify `docs/chapters/chapter-18.md`, `docs/proof-map.md`,
  `docs/clrs-proof-progress.csv`, `CLRSLean/Status.lean`,
  `docs/proof-status-board.md`, and generated `README.md`
  - register seven new contracts;
  - update Chapter 18 from `127/127`, one missing group, to `134/134`, zero
    missing groups;
  - update the repository total from `1491/1491` to `1498/1498`;
  - retain disk/pointer/I/O/RAM work as optional refinements.

## Task 1: Freeze the structural-height contract

**Files:**

- Create: `Tests/Chapter_18_Height_Interface.lean`

- [ ] **Step 1: Add the RED interface**

Create the test with these exact public checks:

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.HeightBound

namespace CLRS.Chapter18.BTree

#check (totalKeys : BTree → Nat)

#check (totalKeys_node :
  ∀ (ks : List Nat) (cs : List BTree),
    totalKeys (node ks cs) = ks.length + (cs.map totalKeys).sum)

#check (nonRoot_totalKeys_add_one_lower_bound :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, ChildBounded tr → Occupancy t false tr → SameDepth tr →
      t ^ (heightOf tr + 1) ≤ totalKeys tr + 1)

#check (wellFormed_empty_or_totalKeys_add_one_lower_bound :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      tr = node [] [] ∨
        2 * t ^ heightOf tr ≤ totalKeys tr + 1)

#check (wellFormed_empty_or_minKeys_le_totalKeys :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      tr = node [] [] ∨ minKeys t (heightOf tr) ≤ totalKeys tr)

#check (wellFormed_minKeys_le_totalKeys :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      tr ≠ node [] [] →
      minKeys t (heightOf tr) ≤ totalKeys tr)

#check (wellFormed_height_log_bound :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2))

example : totalKeys (node [] []) = 0 := by
  native_decide

example :
    heightOf (node [] []) ≤
      Nat.log 2 ((totalKeys (node [] []) + 1) / 2) := by
  native_decide

example :
    heightOf (node [1] []) ≤
      Nat.log 2 ((totalKeys (node [1] []) + 1) / 2) := by
  native_decide

example :
    heightOf (node [2] [node [1] [], node [3] []]) ≤
      Nat.log 2
        ((totalKeys (node [2] [node [1] [], node [3] []]) + 1) / 2) := by
  native_decide

end CLRS.Chapter18.BTree
```

- [ ] **Step 2: Verify the intended RED failure**

Run:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_18_Height_Interface.lean
```

Expected: the import fails because `HeightBound.lean` does not exist.  This is
the intended missing-implementation failure.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_18_Height_Interface.lean
git commit -m "test(ch18): specify structural height bounds"
```

## Task 2: Add exact total-key accounting

**Files:**

- Create:
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean`
- Test: `Tests/Chapter_18_Height_Interface.lean`

- [ ] **Step 1: Define `totalKeys` and its node equation**

Start the module and namespace:

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

namespace CLRS
namespace Chapter18
namespace BTree

open List

def totalKeys (tr : BTree) : Nat := (keysOf tr).length

theorem totalKeys_node (ks : List Nat) (cs : List BTree) :
    totalKeys (node ks cs) =
      ks.length + (cs.map totalKeys).sum := by
  simp [totalKeys, keysOf, List.length_flatMap]
```

Close all namespaces at the end of the file.

- [ ] **Step 2: Prove internal augmented accounting**

Add a private or local helper:

```lean
lemma totalKeys_add_one_eq_sum_children
    {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (hcb : ChildBounded (node ks (c0 :: cs))) :
    totalKeys (node ks (c0 :: cs)) + 1 =
      ((c0 :: cs).map (fun child => totalKeys child + 1)).sum
```

Unfold `ChildBounded` only far enough to obtain
`(c0 :: cs).length = ks.length + 1`.  Rewrite with `totalKeys_node` and
`List.sum_map_add`; simplify the sum of mapped ones to the child-list length.
Finish the linear arithmetic with `omega`.

- [ ] **Step 3: Add small child projections**

Prove file-local helpers for an internal `node ks (c0 :: cs)`:

- every member child inherits `ChildBounded`;
- every member child inherits `Occupancy t false`;
- every member child inherits `SameDepth`;
- every member child has the same height as `c0`.

Reuse `sameDepth_head_sd`, `sameDepth_tail_sd`, and
`sameDepth_children_eq_height` instead of destructing the inductive witness
repeatedly.

- [ ] **Step 4: Run the narrow source check**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
```

Expected: PASS.  The public interface remains RED at the first not-yet-proved
lower-bound theorem.

- [ ] **Step 5: Commit the accounting layer**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
git commit -m "feat(ch18): add exact B-tree key accounting"
```

## Task 3: Prove the non-root power lower bound

**Files:**

- Modify:
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean`

- [ ] **Step 1: Add a list-sum lower-bound helper**

For a list `xs` and functions `f`, prove that a common lower bound `q ≤ f x`
for every member gives:

```lean
xs.length * q ≤ (xs.map f).sum
```

Prefer `List.sum_le_sum` with a constant mapped function; use a short induction
only if simplification of the constant sum is less stable.

- [ ] **Step 2: Prove the public non-root theorem**

Add exactly:

```lean
theorem nonRoot_totalKeys_add_one_lower_bound
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr)
    (hocc : Occupancy t false tr)
    (hsd : SameDepth tr) :
    t ^ (heightOf tr + 1) ≤ totalKeys tr + 1 := by
  ...
```

Induct through `hsd`.

- Leaf:
  - unfold non-root `Occupancy`;
  - obtain `t - 1 ≤ ks.length`;
  - rewrite `heightOf` and `totalKeys`;
  - use `2 ≤ t` to normalize `t - 1 + 1 = t`.
- Internal:
  - obtain at least `t` children from non-root occupancy;
  - apply the induction hypotheses to `c0` and every tail child using the
    projection helpers;
  - rewrite all exponents to the common child height;
  - lift the per-child bound through the list sum;
  - rewrite the sum using `totalKeys_add_one_eq_sum_children`;
  - rewrite node height with `heightOf_internal_of_sameDepth` and
    `Nat.pow_succ`;
  - finish the child-count multiplication inequality.

Do not assume `UniqueKeys`; the theorem counts key slots.

- [ ] **Step 3: Verify source and absence of proof escapes**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
rg -n '\\b(sorry|admit|axiom)\\b' \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
```

Expected: Lean PASS and no unfinished markers.

- [ ] **Step 4: Commit the structural induction**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
git commit -m "feat(ch18): prove non-root key lower bound"
```

## Task 4: Lift the induction to the root and CLRS theorem

**Files:**

- Modify:
  `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean`
- Test: `Tests/Chapter_18_Height_Interface.lean`

- [ ] **Step 1: Prove the root empty-or-power theorem**

Add the exact public statement:

```lean
theorem wellFormed_empty_or_totalKeys_add_one_lower_bound
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    tr = node [] [] ∨
      2 * t ^ heightOf tr ≤ totalKeys tr + 1
```

Destruct `tr` and its children.

- Root leaf:
  - if `ks = []`, return the exact empty tree;
  - otherwise, use root occupancy's lower key bound and simplify height/count.
- Internal root:
  - obtain at least two children from root occupancy;
  - obtain child `ChildBounded`, non-root `Occupancy`, and `SameDepth`;
  - apply `nonRoot_totalKeys_add_one_lower_bound` to each child;
  - sum the common power lower bound across the child list;
  - use exact augmented accounting and
    `heightOf_internal_of_sameDepth`.

- [ ] **Step 2: Derive the `minKeys` wrappers**

Unfold `minKeys` only after obtaining the root augmented inequality.  Use
natural-number arithmetic to prove:

```lean
theorem wellFormed_empty_or_minKeys_le_totalKeys ...
theorem wellFormed_minKeys_le_totalKeys ... (hne : tr ≠ node [] []) ...
```

The second theorem eliminates the empty branch from the first; it must retain
the explicit nonempty premise.

- [ ] **Step 3: Package the logarithmic height theorem**

Add:

```lean
theorem wellFormed_height_log_bound
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2)
```

- Empty branch: substitute `node [] []` and simplify.
- Nonempty branch:
  - turn `2 * t ^ heightOf tr ≤ totalKeys tr + 1` into
    `t ^ heightOf tr ≤ (totalKeys tr + 1) / 2` using
    `(Nat.le_div_iff_mul_le (by omega)).2`, normalizing multiplication order;
  - apply `Nat.le_log_of_pow_le (by omega)`.

- [ ] **Step 4: Turn the interface GREEN**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Height_Interface.lean
```

Expected: both PASS.

- [ ] **Step 5: Commit the root and log capstone**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean \
  Tests/Chapter_18_Height_Interface.lean
git commit -m "feat(ch18): prove logarithmic B-tree height bound"
```

## Task 5: Integrate the final theorem group

**Files:**

- Modify: `CLRSLean/Chapter_18.lean`
- Modify: `literate.toml`
- Modify: `docs/chapters/chapter-18.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-status-board.md`
- Modify: `README.md`

- [ ] **Step 1: Wire the module**

Add:

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.HeightBound
```

to the chapter facade after the Section 18.1 model/search imports.

Register the module as a Section 18.1 child in `literate.toml` and give it a
reader-facing title such as `B-Tree Key Count and Height Bound`.

- [ ] **Step 2: Register the exact public surface**

List all seven contracts in the Chapter 18 guide and proof map.  Explain that:

- the structural theorem counts key slots, so it does not require uniqueness;
- empty roots are represented by a disjunction;
- the logarithmic theorem is universal over `WellFormed`;
- the old `minKeys_lower_bound` is only an expression-level fact, while the new
  theorem connects the expression to a real tree.

- [ ] **Step 3: Update machine-readable status**

Change Chapter 18 to:

- `repo_status = main-proof-complete-for-correctness`;
- `tracked_key_theorems = 134`;
- `proved_tracked_theorems = 134`;
- `missing_core_groups = 0`;
- `remaining_core_groups = None`.

Add the new module/test to the evidence field.  Keep low-level disk/pointer/I/O
and RAM semantics in the notes as optional refinements.

Regenerate README's status table with `scripts/gen_readme_table.py` rather than
editing the generated block by hand.

- [ ] **Step 4: Run the Chapter 18 gate**

Run:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Height_Interface.lean
lake env lean -DwarningAsError=true CLRSLean/Chapter_18.lean
lake build CLRSLean.Chapter_18
for f in Tests/Chapter_18*.lean; do
  lake env lean -DwarningAsError=true "$f" || exit 1
done
python3 scripts/check_progress_csv.py
python3 scripts/gen_readme_table.py --check
python3 scripts/test_literate_config.py
python3 scripts/check_site_consistency.py
rg -n '\\b(sorry|admit|axiom)\\b' \
  CLRSLean/Chapter_18 Tests/Chapter_18*.lean
git diff --check
```

Expected:

- focused source/interface/facade checks PASS;
- Chapter 18 build PASS;
- all ten Chapter 18 tests PASS with warnings as errors;
- progress reports 35 chapters and `1498/1498`;
- README/config/site consistency checks PASS;
- unfinished-marker scan has no proof escapes in the new work;
- clean diff whitespace.

Do not run `lake build :literateHtml`.

- [ ] **Step 5: Commit the integration milestone**

```bash
git add \
  CLRSLean/Chapter_18.lean \
  literate.toml \
  docs/chapters/chapter-18.md \
  docs/proof-map.md \
  docs/clrs-proof-progress.csv \
  CLRSLean/Status.lean \
  docs/proof-status-board.md \
  README.md
git commit -m "docs(ch18): register logarithmic height correctness"
```

## Task 6: Independent review and final verification

- [ ] **Step 1: Request specification review**

Review the proof against
`docs/superpowers/specs/2026-07-31-ch18-height-bound-design.md`:

- exact seven-contract surface;
- legal empty-root boundary;
- no hidden uniqueness premise;
- correct exponent and division/log direction;
- no low-level refinement overclaim.

- [ ] **Step 2: Request code-quality review**

Review the focused module for:

- reuse of existing `SameDepth` and occupancy projections;
- stable structural induction;
- no unnecessary imports or duplicated split/insertion machinery;
- no proof escape or false theorem strengthening.

- [ ] **Step 3: Re-run changed-scope verification after fixes**

If review causes any edit, rerun at least:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Height_Interface.lean
lake build CLRSLean.Chapter_18
git diff --check
```

Commit review fixes separately.

- [ ] **Step 4: Confirm clean handoff**

```bash
git status --short
git log --oneline -12
```

Expected: clean worktree, all height-bound commits present, and no full-site
HTML generation.
