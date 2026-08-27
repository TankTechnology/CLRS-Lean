# Chapter 7 Quicksort Operational Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the explicit CLRS pair-trace counter equals the recursive executable quicksort comparison counter pointwise, then transfer the exact expectation and `Theta(n log n)` result to the operational counter.

**Architecture:** Normalize both counters to the total depth of the binary search tree built from the same priority permutation.  One focused module proves execution-to-depth by fuel induction, another proves pair-trace-to-depth through Chapter 12's first-in-interval/ancestor theorem, and a thin aggregator composes the equalities.

**Tech Stack:** Lean 4.32, Mathlib finite sums and lists, CLRS-Lean Chapter 7 quicksort, CLRS-Lean Chapter 12 randomly built BSTs, repository trust macros.

---

## File structure

- `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/UnorderedPairs.lean`: generic strict-pair triangular sum identity.
- `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/ExecutionToBST.lean`: duplicate-free quicksort cost equals the depth sum of the BST built from the same list.
- `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/PairTraceToBST.lean`: CLRS pair predicate and pair counter equal BST ancestor semantics and total depth.
- `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge.lean`: public pointwise and expectation bridge.
- `Tests/FourthEdition_Chapter_07_Interface.lean`: public theorem names and finite executable examples.
- `Tests/Trust/Chapter_07.lean`: project-axiom audit for the new headline theorems.
- `CLRSLean/FourthEdition/Chapter_07.lean`, `docs/clrs-fourth-edition-map.csv`, and `literate.toml`: reader-facing integration.

### Task 1: Pin the public interface with a failing test

**Files:**
- Modify: `Tests/FourthEdition_Chapter_07_Interface.lean`

- [ ] **Step 1: Add the desired public checks**

```lean
#check randomizedQuicksortComparisonCount_eq_quickSortComparisons
#check operationalRandomizedQuicksortExpectedComparisons
#check operationalRandomizedQuicksortExpectedComparisons_eq
#check operationalRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn
```

- [ ] **Step 2: Verify the interface fails for the expected reason**

Run:

```text
lake env lean Tests/FourthEdition_Chapter_07_Interface.lean
```

Expected result: nonzero exit with unknown identifiers for the four new public names, while existing declarations still elaborate.

- [ ] **Step 3: Commit the red interface checkpoint**

```text
git add Tests/FourthEdition_Chapter_07_Interface.lean
git commit -m "test(ch07): pin operational quicksort bridge interface (#330)"
```

### Task 2: Prove the finite unordered-pair sum identity

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/UnorderedPairs.lean`

- [ ] **Step 1: State the generic theorem over `Fin n`**

```lean
/-- Summing both orientations of every strict pair is the same as summing an
off-diagonal matrix. -/
theorem sum_offDiagonal_eq_sum_strictPairs {n : Nat}
    (f : Fin n -> Fin n -> Nat) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n,
        if i.val < j.val then f i j + f j i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Fin.sum_univ_succ]
      simp [ih]
```

If the final `simp` exposes associativity or sum-distribution goals, normalize only those goals with `Finset.sum_add_distrib`, `add_assoc`, `add_left_comm`, and `add_comm`; do not specialize the theorem to quicksort.

- [ ] **Step 2: Elaborate the new file directly**

Run:

```text
lake env lean CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/UnorderedPairs.lean
```

Expected result: exit 0 with no unfinished proof declaration.

- [ ] **Step 3: Commit the combinatorial layer**

```text
git add CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/UnorderedPairs.lean
git commit -m "feat(ch07): prove unordered-pair sum identity (#330)"
```

### Task 3: Connect recursive execution to BST total depth

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/ExecutionToBST.lean`

- [ ] **Step 1: Add the list/BST normalization definitions and partition bridge**

```lean
/-- Sum of search depths for the keys in `xs`. -/
def bstDepthSumOn (xs : List Nat) (t : Chapter12.BSTree) : Nat :=
  (xs.map (fun x => Chapter12.depth x t)).sum

/-- On a duplicate-free pivot call, the quicksort `<= pivot` partition is the
BST's strict `< pivot` partition. -/
theorem partitionAround_left_eq_filter_lt_of_nodup
    (pivot : Nat) (tail : List Nat) (h : (pivot :: tail).Nodup) :
    (partitionAround pivot tail).1 = tail.filter (fun x => decide (x < pivot)) := by
  rw [partitionAround_left_eq_filter]
  apply List.filter_congr
  intro x hx
  have hne : x ≠ pivot := by
    exact fun hxp => h.1 (hxp ▸ hx)
  simp only [decide_eq_decide]
  omega
```

- [ ] **Step 2: Prove the fuelled execution/depth theorem**

Add a theorem with the exact interface:

```lean
theorem quickSortComparisonsFuel_eq_bstDepthSumOn
    (fuel : Nat) (xs : List Nat) (hlen : xs.length <= fuel)
    (hnodup : xs.Nodup) :
    quickSortComparisonsFuel fuel xs =
      bstDepthSumOn xs (Chapter12.buildFromList xs)
```

Prove it by induction on `fuel`, splitting `xs`.  In the nonempty case:

1. rewrite `Chapter12.buildFromList_cons`;
2. rewrite the quicksort left partition using `partitionAround_left_eq_filter_lt_of_nodup`;
3. apply the induction hypothesis to the strict left and right filters;
4. use `partitionAround_perm`, mapped by the depth function, to split the tail sum;
5. simplify `Chapter12.depth` for keys known `< pivot` or `> pivot`;
6. close the remaining length equality with `partitionAround_length_add` and `omega`.

- [ ] **Step 3: Specialize to a permutation sample**

Expose the following two theorems:

```lean
theorem randomizedQuicksortInput_eq_permKeys {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortInput priority = Chapter12.permKeys priority := rfl

theorem quickSortComparisons_randomizedInput_eq_totalDepth {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    quickSortComparisons (randomizedQuicksortInput priority) =
      ∑ j : Fin n,
        Chapter12.depth j.val (Chapter12.buildFromPerm priority)
```

Obtain `Nodup` from `randomizedQuicksortInput_perm_range priority` and
`List.nodup_range n`.  Rewrite `bstDepthSumOn` over `List.finRange n` to the
`Fin n` sum with `Fin.sum_univ_eq_sum_range`.

- [ ] **Step 4: Elaborate the execution module**

Run:

```text
lake build CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees
lake env lean CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/ExecutionToBST.lean
```

Expected result: both commands exit 0.

- [ ] **Step 5: Commit the execution bridge**

```text
git add CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/ExecutionToBST.lean
git commit -m "feat(ch07): relate quicksort comparisons to BST depth (#330)"
```

### Task 4: Connect the CLRS pair trace to BST total depth

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/PairTraceToBST.lean`

- [ ] **Step 1: Prove the interval representation bridge**

Add:

```lean
theorem rangeFin_eq_intervalIcc (n i j : Nat) (hij : i < j) (hjn : j < n) :
    rangeFin n i j (Nat.le_of_lt hij) hjn =
      Finset.Icc (show Fin n from ⟨i, Nat.lt_trans hij hjn⟩)
        (show Fin n from ⟨j, hjn⟩)
```

Use `Finset.ext`, unfold `rangeFin`, and reduce membership on both sides to
`i <= k.val && k.val <= j`.

- [ ] **Step 2: Prove the pointwise event characterization**

```lean
theorem comparedInQuicksort_iff_ancestor {n : Nat} (i j : Fin n)
    (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) :
    comparedInQuicksort n i.val j.val hij j.isLt priority <->
      Chapter12.isAncestorOf i.val j.val (Chapter12.buildFromPerm priority) \/
      Chapter12.isAncestorOf j.val i.val (Chapter12.buildFromPerm priority)
```

Rewrite `rangeFin` to `Finset.Icc`, unfold Chapter 7 `IsFirstIn` and `pos`,
rewrite Chapter 12 `firstInInterval_iff_isFirstOf`, and use
`Chapter12.isAncestorOf_buildFromPerm_iff_firstInInterval` in both
orientations.

- [ ] **Step 3: Express one key's depth as strict ancestor bits**

```lean
theorem depth_eq_sum_strictAncestorBits {n : Nat}
    (priority : Equiv.Perm (Fin n)) (j : Fin n) :
    Chapter12.depth j.val (Chapter12.buildFromPerm priority) =
      ∑ i : Fin n,
        if i ≠ j ∧ Chapter12.isAncestorOf i.val j.val
            (Chapter12.buildFromPerm priority) then 1 else 0
```

Use `Chapter12.ancestorCount_eq_depth_add_one`,
`Chapter12.ancestorCount_eq_sum`, `Chapter12.buildFromList_ordered`, and
`Chapter12.InTree_buildFromPerm_lt`.  Split the self term with
`Finset.sum_erase_add` and discharge self-ancestry with
`Chapter12.isAncestorOf_self_buildFromPerm`.

- [ ] **Step 4: Prove pair-trace count equals total depth**

```lean
theorem randomizedQuicksortComparisonCount_eq_totalDepth {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortComparisonCount priority =
      ∑ j : Fin n,
        Chapter12.depth j.val (Chapter12.buildFromPerm priority)
```

Expand the pair counter, rewrite each pair event with
`comparedInQuicksort_iff_ancestor`, rewrite total depth with
`depth_eq_sum_strictAncestorBits`, commute the double sum, and apply
`sum_offDiagonal_eq_sum_strictPairs`.  Prove the two ancestor orientations are
exclusive for distinct keys using the first-in-interval characterization and
injectivity of `priority.symm`; this turns the disjunction bit into the sum of
the two orientation bits.

- [ ] **Step 5: Elaborate and commit the pair module**

Run:

```text
lake env lean CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/PairTraceToBST.lean
```

Expected result: exit 0.

Commit:

```text
git add CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge/PairTraceToBST.lean
git commit -m "feat(ch07): identify pair trace with BST depth (#330)"
```

### Task 5: Close the public pointwise and expectation bridge

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_07.lean`
- Modify: `Tests/FourthEdition_Chapter_07_Interface.lean`
- Modify: `Tests/Trust/Chapter_07.lean`

- [ ] **Step 1: Compose the pointwise equality**

```lean
theorem randomizedQuicksortComparisonCount_eq_quickSortComparisons
    {n : Nat} (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortComparisonCount priority =
      quickSortComparisons (randomizedQuicksortInput priority) := by
  rw [randomizedQuicksortComparisonCount_eq_totalDepth,
    quickSortComparisons_randomizedInput_eq_totalDepth]
```

- [ ] **Step 2: Define and close the operational expectation**

```lean
noncomputable def operationalRandomizedQuicksortExpectedComparisons
    (n : Nat) : Real :=
  fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
    (quickSortComparisons (randomizedQuicksortInput priority) : Real))

theorem operationalRandomizedQuicksortExpectedComparisons_eq_explicit
    (n : Nat) :
    operationalRandomizedQuicksortExpectedComparisons n =
      explicitRandomizedQuicksortExpectedComparisons n := by
  unfold operationalRandomizedQuicksortExpectedComparisons
    explicitRandomizedQuicksortExpectedComparisons
  apply congrArg fintypeExpect
  funext priority
  exact_mod_cast
    (randomizedQuicksortComparisonCount_eq_quickSortComparisons priority).symm

theorem operationalRandomizedQuicksortExpectedComparisons_eq (n : Nat) :
    operationalRandomizedQuicksortExpectedComparisons n =
      expectedComparisonsReal n := by
  rw [operationalRandomizedQuicksortExpectedComparisons_eq_explicit,
    explicitRandomizedQuicksortExpectedComparisons_eq]

theorem operationalRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn :
    Chapter03.isBigTheta operationalRandomizedQuicksortExpectedComparisons
      (fun n : Nat => (n : Real) * Real.log (n : Real)) := by
  rw [show operationalRandomizedQuicksortExpectedComparisons =
      explicitRandomizedQuicksortExpectedComparisons by
    funext n
    exact operationalRandomizedQuicksortExpectedComparisons_eq_explicit n]
  exact explicitRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn
```

- [ ] **Step 3: Make the interface green and add finite examples**

Import `OperationalBridge` from `CLRSLean/FourthEdition/Chapter_07.lean`, then
add:

```lean
example :
    randomizedQuicksortComparisonCount (Equiv.refl (Fin 4)) =
      quickSortComparisons (randomizedQuicksortInput (Equiv.refl (Fin 4))) := by
  native_decide

example :
    randomizedQuicksortComparisonCount (Equiv.swap (0 : Fin 3) 1) =
      quickSortComparisons
        (randomizedQuicksortInput (Equiv.swap (0 : Fin 3) 1)) := by
  native_decide
```

Run:

```text
lake build CLRSLean.FourthEdition.Chapter_07
lake env lean Tests/FourthEdition_Chapter_07_Interface.lean
```

Expected result: both commands exit 0 and the four checks from Task 1 resolve.

- [ ] **Step 4: Extend the trust surface**

Add `#check` and `#assert_axioms` for:

```lean
CLRS.Chapter07.randomizedQuicksortComparisonCount_eq_quickSortComparisons
CLRS.Chapter07.operationalRandomizedQuicksortExpectedComparisons_eq
CLRS.Chapter07.operationalRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn
```

Run:

```text
lake env lean Tests/Trust/Chapter_07.lean
```

Expected result: exit 0; the accepted kernel dependencies are only Lean/Mathlib
axioms such as `propext`, `Classical.choice`, and `Quot.sound`, with no project
axiom and no `sorryAx`.

- [ ] **Step 5: Commit the public closure**

```text
git add CLRSLean/FourthEdition/Chapter_07.lean CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge.lean Tests/FourthEdition_Chapter_07_Interface.lean Tests/Trust/Chapter_07.lean
git commit -m "feat(ch07): close operational quicksort counter bridge (#330)"
```

### Task 6: Synchronize reader-facing metadata and run final verification

**Files:**
- Modify: `CLRSLean/FourthEdition/Chapter_07.lean`
- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `literate.toml`

- [ ] **Step 1: Update the chapter guide and edition map**

State that the pair trace and recursive counter are pointwise equal.  Remove
the pointwise refinement item from `## Current Gaps`; retain mutable-array/RAM
refinement and tail-bound/lower-bound items.  Add the operational bridge module
to the §7.3 source list in `docs/clrs-fourth-edition-map.csv`.

- [ ] **Step 2: Register all four new modules in `literate.toml`**

Place the operational bridge modules after the existing explicit-randomness
bridge, in dependency order: `UnorderedPairs`, `ExecutionToBST`,
`PairTraceToBST`, then `OperationalBridge`.  Give each module a distinct
reader-facing title.

- [ ] **Step 3: Run the focused and repository verification gates**

Run:

```text
lake build CLRSLean.FourthEdition.Chapter_07
lake env lean Tests/FourthEdition_Chapter_07_Interface.lean
lake env lean Tests/Trust/Chapter_07.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/FourthEdition/Chapter_07/Section_07_3_Randomized_Quicksort/ExplicitRandomness/OperationalBridge Tests/FourthEdition_Chapter_07_Interface.lean Tests/Trust/Chapter_07.lean
git diff --check
python3 scripts/check_repository.py
lake build CLRSLean
```

Expected result: all Lean and repository commands exit 0; the placeholder scan
finds no unfinished proof declaration in the new modules.

- [ ] **Step 4: Commit documentation and metadata**

```text
git add CLRSLean/FourthEdition/Chapter_07.lean docs/clrs-fourth-edition-map.csv literate.toml
git commit -m "docs(ch07): record operational quicksort closure (#330)"
```

- [ ] **Step 5: Integrate after final review**

Fast-forward the verified branch into `main`, push `main`, comment on #330 with
the pointwise theorem and verification evidence, and close #330.  Confirm that
local `main`, `origin/main`, and the reported commit SHA agree.  Do not trigger
the manual website workflow as part of this proof task.
