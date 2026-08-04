# Chapter 27 Parallel Merge and Merge Sort Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the actual CLRS midpoint/binary-search P-MERGE and P-MERGE-SORT algorithms, prove sortedness and permutation preservation, and derive execution-attached worst-case `Theta(n)`/`Theta(log^2 n)` and `Theta(n log n)`/`Theta(log^3 n)` work/span theorems.

**Architecture:** A costed lower-bound binary search supplies the split rank.  P-MERGE normalizes its two inputs so the primary list is longer, removes its midpoint pivot, and recursively merges the lower and upper partitions in parallel; P-MERGE-SORT recursively sorts list halves in parallel and sequentially composes with P-MERGE.  Structural split theorems feed strengthened work induction and three-quarter span envelopes, while explicit even/odd and recursively interleaved inputs witness the matching worst cases.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `List` sorted/permutation APIs, Chapter 3 asymptotics, Chapter 4 all-input transfer, Chapter 27 `Costed`, Lake, Verso.

---

## Prerequisite

Complete the foundation/scheduler plan and Task 2 of the matrix plan so
`Costed` and the split recurrence modules exist.  The matrix correctness and
cost theorems may proceed independently after that shared prerequisite.

## File Map

- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Definitions.lean` for lower-bound search and P-MERGE execution.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Correctness.lean` for binary-search partition and merge correctness.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean` for structural shrink, work, span, and worst-case witnesses.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Definitions.lean`.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Correctness.lean`.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs.lean`.
- Create `Tests/Chapter_27_ParallelMerge_Interface.lean`.
- Modify `literate.toml` and `docs/index.md` to register all six modules.

### Task 1: Lock the Parallel-Merge Interface in RED

**Files:**
- Create: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Add the intended public checks**

Create:

```lean
import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check binaryLowerBound
#check binaryLowerBound_index_le_length
#check binaryLowerBound_partition
#check binaryLowerBound_work_le_log

end CLRS.Chapter27
```

- [ ] **Step 2: Verify RED and commit**

```bash
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
```

Expected: nonzero exit with `Unknown constant CLRS.Chapter27.binaryLowerBound`.

```bash
git add Tests/Chapter_27_ParallelMerge_Interface.lean
git commit -m "test(ch27): specify parallel merge algorithms"
```

### Task 2: Implement Costed Lower-Bound Binary Search

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Definitions.lean`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Define the interval search**

Import `S1_CostModel`.  Define a private total helper over half-open bounds:

```lean
private def binaryLowerBoundLoop [LinearOrder α]
    (xs : List α) (pivot : α) (lo hi : ℕ) : Costed ℕ :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    match xs[mid]? with
    | none => Costed.charge 1 1 lo
    | some x =>
        if x < pivot then
          Costed.seq (Costed.charge 1 1 ())
            (fun _ => binaryLowerBoundLoop xs pivot (mid + 1) hi)
        else
          Costed.seq (Costed.charge 1 1 ())
            (fun _ => binaryLowerBoundLoop xs pivot lo mid)
  else
    Costed.pure lo
termination_by hi - lo
```

Discharge both decreasing obligations from `lo < hi` and midpoint arithmetic.
The `none` branch keeps the function total outside its intended invariant; the
public wrapper never reaches it.

Define:

```lean
def binaryLowerBound [LinearOrder α] (xs : List α) (pivot : α) : Costed ℕ :=
  binaryLowerBoundLoop xs pivot 0 xs.length
```

- [ ] **Step 2: Add direct execution tests**

Use `native_decide` to check indices for empty lists, duplicates, a pivot below
all elements, between elements, equal to repeated elements, and above all
elements.  Check that `.work = .span` for these sequential searches.

- [ ] **Step 3: Build the definition module**

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Definitions
```

Expected: success.

### Task 3: Prove Binary-Search Partition and Cost

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Correctness.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: State the bundled lower-bound result**

Define:

```lean
structure LowerBoundSpec [LinearOrder α] (xs : List α) (pivot : α) (i : ℕ) : Prop where
  index_le_length : i ≤ xs.length
  left_lt : ∀ x ∈ xs.take i, x < pivot
  right_ge : ∀ x ∈ xs.drop i, pivot ≤ x
```

- [ ] **Step 2: Prove the loop invariant**

Prove `binaryLowerBoundLoop_correct` for premises
`lo ≤ hi`, `hi ≤ xs.length`, every element before `lo` is below the pivot,
every element at or after `hi` is at least the pivot, and `xs.Sorted (· ≤ ·)`.
In each branch use sortedness to extend the appropriate boundary invariant and
use `List.get?_eq_getElem?`/membership-at-index lemmas to eliminate `none`.

- [ ] **Step 3: Publish wrapper theorems**

```lean
theorem binaryLowerBound_partition [LinearOrder α] (xs : List α) (pivot : α)
    (hxs : xs.Sorted (· ≤ ·)) :
    LowerBoundSpec xs pivot (binaryLowerBound xs pivot).value

theorem binaryLowerBound_index_le_length [LinearOrder α]
    (xs : List α) (pivot : α) :
    (binaryLowerBound xs pivot).value ≤ xs.length

theorem binaryLowerBound_work_le_log [LinearOrder α]
    (xs : List α) (pivot : α) :
    (binaryLowerBound xs pivot).work ≤ Nat.log 2 xs.length + 1
```

Prove the work bound by interval-length strong induction.  Publish the equal
span corollary for the sequential search.

- [ ] **Step 4: Import, register, run GREEN, and commit**

Import ParallelMerge Definitions and Correctness from the historical
aggregator and register both paths.  Then run the committed interface without
commenting or deleting any check:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Correctness
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): prove binary lower bound correct"
```

### Task 4: Implement the Actual CLRS P-MERGE Control Structure

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Definitions.lean`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Extend the interface and verify RED**

Append checks for `pMerge`, `pMerge_value_sorted`, `pMerge_value_perm`,
`pMerge_value_length`, and `pMerge_correct`.  Run the focused interface and
expect a nonzero exit at `pMerge`, after every binary-search check resolves.

- [ ] **Step 2: Define normalized split data**

Add a documented `MergeSplit` structure containing the normalized primary and
secondary lists, midpoint `i`, pivot, lower-bound index `j`, and the four
`take`/`drop` partitions.  Define `mergeSplit` only for nonempty total input;
its proof arguments establish the pivot index is valid.

- [ ] **Step 3: Define P-MERGE by total length**

Use this public type:

```lean
def pMerge [LinearOrder α] : List α → List α → Costed (List α)
```

At each call, bind `primary, secondary` with an `if` on lengths instead of
recursing merely to swap arguments.  The empty-total branch returns
`Costed.pure []`.  Otherwise:

1. choose `i = primary.length / 2` and its pivot;
2. sequentially run `binaryLowerBound secondary pivot` to obtain `j`;
3. recursively merge `primary.take i` with `secondary.take j` and
   `primary.drop (i + 1)` with `secondary.drop j`;
4. combine both calls with `Costed.par`; and
5. map the values to `lower ++ pivot :: upper` while charging one unit for
   pivot placement.

Use `xs.length + ys.length` as the termination measure.  Prove both recursive
totals strictly decrease because the pivot is removed.

- [ ] **Step 4: Add concrete algorithm tests**

```lean
example : (pMerge ([] : List ℕ) []).value = [] := by native_decide
example : (pMerge [1, 3, 5] [2, 4, 6]).value = [1, 2, 3, 4, 5, 6] := by native_decide
example : (pMerge [1, 2, 2] [2, 2, 3]).value = [1, 2, 2, 2, 2, 3] := by native_decide
example : (pMerge [1, 4] [2, 3, 5]).value = [1, 2, 3, 4, 5] := by native_decide
```

- [ ] **Step 5: Build definitions and commit**

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Definitions
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Definitions.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean
git commit -m "feat(ch27): implement midpoint binary-search parallel merge"
```

### Task 5: Prove P-MERGE Sortedness and Element Preservation

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Correctness.lean`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Add partition and boundary lemmas**

Prove that normalized primary/secondary inputs remain sorted, all elements in
the lower primary/secondary partitions are at most the pivot, and the pivot is
at most every element in the upper partitions.  Use
`binaryLowerBound_partition` for the secondary side and sorted-list take/drop
facts for the primary side.

- [ ] **Step 2: Add a bundled merge result predicate**

```lean
structure PMergeSpec [LinearOrder α]
    (xs ys out : List α) : Prop where
  sorted : out.Sorted (· ≤ ·)
  perm : out.Perm (xs ++ ys)
  length_eq : out.length = xs.length + ys.length
```

- [ ] **Step 3: Prove `pMerge_correct` by strong induction**

Induct on `xs.length + ys.length`.  Rewrite the Costed value through the
binary-search sequential step and parallel pair, apply the two recursive
hypotheses, join sorted lists through the pivot using the boundary lemmas, and
compose `List.Perm` through take/drop reconstruction and the normalization
swap.

Publish:

```lean
theorem pMerge_correct [LinearOrder α] (xs ys : List α)
    (hxs : xs.Sorted (· ≤ ·)) (hys : ys.Sorted (· ≤ ·)) :
    PMergeSpec xs ys (pMerge xs ys).value

theorem pMerge_value_sorted [LinearOrder α] (xs ys : List α)
    (hxs : xs.Sorted (· ≤ ·)) (hys : ys.Sorted (· ≤ ·)) :
    (pMerge xs ys).value.Sorted (· ≤ ·)

theorem pMerge_value_perm [LinearOrder α] (xs ys : List α)
    (hxs : xs.Sorted (· ≤ ·)) (hys : ys.Sorted (· ≤ ·)) :
    (pMerge xs ys).value.Perm (xs ++ ys)

theorem pMerge_value_length [LinearOrder α] (xs ys : List α)
    (hxs : xs.Sorted (· ≤ ·)) (hys : ys.Sorted (· ≤ ·)) :
    (pMerge xs ys).value.length = xs.length + ys.length
```

- [ ] **Step 4: Exercise direct wrappers and commit**

Add theorem-application examples for duplicates and odd total length, then:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Correctness
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Correctness.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean
git commit -m "feat(ch27): prove parallel merge correct"
```

Expected: the interface exits 0 and all P-MERGE correctness checks resolve.

### Task 6: Prove the Three-Quarter Structural Bound

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Extend the structural interface and verify RED**

Append checks for `pMerge_childSizes_add_one` and
`pMerge_childSize_le_threeQuarters`.  Run the interface and expect a nonzero
exit at the first newly added name.

- [ ] **Step 2: Expose child-size equations from `MergeSplit`**

For a nonempty normalized split with total `n`, define `leftSize` and
`rightSize` and prove:

```lean
theorem pMerge_childSizes_add_one (S : MergeSplit α) :
    S.leftSize + S.rightSize + 1 = S.totalSize

theorem pMerge_childSize_le_threeQuarters (S : MergeSplit α) :
    S.leftSize ≤ S.totalSize - S.totalSize / 4 ∧
    S.rightSize ≤ S.totalSize - S.totalSize / 4
```

Use `primary.length ≥ secondary.length`, `i = primary.length / 2`,
`j ≤ secondary.length`, and `omega`.  Handle totals below four explicitly.

- [ ] **Step 3: Prove execution recurrence inequalities**

Unfold one P-MERGE step and prove exact work/span equations in terms of the
actual split and binary-search cost.  Derive public one-step upper inequalities
using `binaryLowerBound_work_le_log` and the three-quarter theorem.

- [ ] **Step 4: Import costs, run GREEN, and commit the structural spine**

Import ParallelMerge Costs from the historical aggregator and register its
path/title before running the interface:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): prove parallel merge split bounds"
```

### Task 7: Prove P-MERGE Linear Work

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Extend the work interface and verify RED**

Append checks for `pMerge_work_lower` and `pMerge_work_upper`.  Run the
interface and expect a nonzero exit at `pMerge_work_lower`.

- [ ] **Step 2: Prove the direct lower bound**

Because every nonempty recursive node places exactly one pivot and the child
sizes partition the remaining elements, prove by strong induction:

```lean
theorem pMerge_work_lower [LinearOrder α] (xs ys : List α) :
    xs.length + ys.length ≤ (pMerge xs ys).work + 1
```

- [ ] **Step 3: Prove the strengthened linear upper invariant**

Use the strengthened natural inequality

```text
pMerge.work + 8 * (log(total + 1)) ≤ 64 * total + 64
```

The induction step uses child-size sum, both child lower/upper quarter bounds,
and a lemma lower-bounding the sum of child logarithms.  Prove all totals below
the induction threshold by `native_decide` or `interval_cases`; close the large
case with `omega`/`nlinarith` after isolating logarithm facts.  Publish the
projection:

```lean
theorem pMerge_work_upper [LinearOrder α] (xs ys : List α) :
    (pMerge xs ys).work ≤ 64 * (xs.length + ys.length + 1)
```

Do not replace this target with `O(n log n)`; linear work is a main-text gate.

- [ ] **Step 4: Add representative work-bound examples and commit**

```bash
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean
git commit -m "feat(ch27): prove parallel merge linear work"
```

### Task 8: Prove P-MERGE Worst-Case Quadratic-Log Span

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Extend the span interface and verify RED**

Append checks for `pMerge_span_upper` and
`pMerge_interleaved_span_lower`.  Run the interface and expect a nonzero exit
at `pMerge_span_upper`.

- [ ] **Step 2: Define and solve the three-quarter span envelope**

Define a natural recurrence `pMergeSpanUpper` whose recursive argument is
`n - n / 4` and whose level charge is `Nat.log 2 n + 4`.  Prove every actual
P-MERGE span is bounded by it, using monotonicity and the child-size theorem.
Prove:

```lean
theorem pMerge_span_upper [LinearOrder α] (xs ys : List α) :
    (pMerge xs ys).span ≤
      64 * (Nat.log 2 (xs.length + ys.length) + 1) ^ 2
```

Show that two applications of the three-quarter shrink reduce the binary
logarithm by at least one above a fixed base threshold; solve the envelope by
strong induction on the logarithm.

- [ ] **Step 3: Define interleaved sorted witnesses**

```lean
def evenKeys (n : ℕ) : List ℕ := (List.range n).map (fun i => 2 * i)
def oddKeys (n : ℕ) : List ℕ := (List.range n).map (fun i => 2 * i + 1)
```

Prove both lists sorted, prove the lower-bound index of the even-list midpoint
in `oddKeys n`, and show the larger recursive child retains the same
interleaving form up to an order-preserving offset.

- [ ] **Step 4: Prove the matching lower witness**

On sizes `2^k`, prove an explicit quadratic lower polynomial in `k` for
`(pMerge (evenKeys (2^k)) (oddKeys (2^k))).span`.  Publish:

```lean
theorem pMerge_interleaved_span_lower (k : ℕ) :
    (k + 1) ^ 2 ≤
      8 * (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span
```

The factor eight absorbs the first two boundary levels while retaining a
uniform, explicit quadratic lower witness.

- [ ] **Step 5: Test, inspect axioms, and commit**

```bash
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge -g '*.lean'
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean
git commit -m "feat(ch27): prove parallel merge span bound"
```

### Task 9: Implement and Prove P-MERGE-SORT Correct

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Definitions.lean`
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Correctness.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Extend the merge-sort interface and verify RED**

Append checks for `pMergeSort`, `pMergeSort_value_sorted`,
`pMergeSort_value_perm`, `pMergeSort_value_length`, and
`pMergeSort_correct`.  Run the interface and expect a nonzero exit at
`pMergeSort`.

- [ ] **Step 2: Define the recursive execution**

```lean
def pMergeSort [LinearOrder α] (xs : List α) : Costed (List α) :=
  if h : xs.length ≤ 1 then
    Costed.charge xs.length xs.length xs
  else
    let left := xs.take (xs.length / 2)
    let right := xs.drop (xs.length / 2)
    Costed.seq (Costed.par (pMergeSort left) (pMergeSort right))
      (fun sorted => pMerge sorted.1 sorted.2)
termination_by xs.length
```

Use the established floor/ceiling length lemmas for both decreasing goals.

- [ ] **Step 3: Prove the bundled result**

Define `PMergeSortSpec xs out` with sortedness, permutation, and length fields.
Induct on input length, apply both recursive specs, then apply `pMerge_correct`.
Publish `pMergeSort_correct`, `pMergeSort_value_sorted`,
`pMergeSort_value_perm`, and `pMergeSort_value_length`.

- [ ] **Step 4: Add concrete examples**

Exercise empty, singleton, reverse odd-length, and duplicate-heavy inputs with
`native_decide`.

- [ ] **Step 5: Import, register, build, run, and commit**

Import ParallelMergeSort Definitions and Correctness from the historical
aggregator and register both modules, then run:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Correctness
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): prove parallel merge sort correct"
```

### Task 10: Prove P-MERGE-SORT Work and Span

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `Tests/Chapter_27_ParallelMerge_Interface.lean`

- [ ] **Step 1: Extend the cost interface and verify RED**

Append checks for `pMergeSort_work_lower`, `pMergeSort_work_upper`,
`pMergeSort_span_upper`, and `pMergeSort_worstFamily_span_lower`.  Run the
interface and expect a nonzero exit at the first newly added name.

- [ ] **Step 2: Derive pointwise work bounds**

Unfold the execution through `Costed.par` and `Costed.seq`.  Combine the two
recursive costs with P-MERGE's linear bounds to prove explicit constants:

```lean
theorem pMergeSort_work_lower [LinearOrder α] (xs : List α) :
    xs.length * (Nat.log 2 xs.length + 1) ≤
      16 * ((pMergeSort xs).work + xs.length + 1)

theorem pMergeSort_work_upper [LinearOrder α] (xs : List α) :
    (pMergeSort xs).work ≤
      128 * (xs.length + 1) * (Nat.log 2 xs.length + 1)
```

Prove by strong induction, using the floor/ceiling split and the already proved
P-MERGE bounds.

- [ ] **Step 3: Prove the universal cubic-log span upper bound**

Combine the maximum recursive-sort span with `pMerge_span_upper`, then sum the
quadratic logarithmic merge charges across `O(log n)` recursion levels:

```lean
theorem pMergeSort_span_upper [LinearOrder α] (xs : List α) :
    (pMergeSort xs).span ≤
      256 * (Nat.log 2 xs.length + 1) ^ 3
```

- [ ] **Step 4: Define a recursive worst-case input**

```lean
def worstMergeSortInput : ℕ → List ℕ
  | 0 => [0]
  | k + 1 =>
      (worstMergeSortInput k).map (fun x => 2 * x) ++
      (worstMergeSortInput k).map (fun x => 2 * x + 1)
```

Prove its length is `2^k`; after the two recursive sorts its halves are the
even and odd sorted keys, so the final P-MERGE realizes the interleaved span
witness.

- [ ] **Step 5: Prove the matching span lower bound**

Publish a concrete positive constant theorem:

```lean
theorem pMergeSort_worstFamily_span_lower (k : ℕ) :
    (k + 1) ^ 3 ≤
      64 * (pMergeSort (worstMergeSortInput k)).span
```

Use induction on `k`, the P-MERGE interleaved lower theorem, and the exact
sequential addition of merge span after the parallel recursive sorts.

- [ ] **Step 6: Import costs, add axiom prints, and commit**

Add `#print axioms` for P-MERGE/P-MERGE-SORT correctness and the four headline
cost bounds.  Import and register ParallelMergeSort Costs before running the
focused test, then commit:

```bash
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_ParallelMerge_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): prove parallel merge sort asymptotics"
```

### Task 11: Verify the Merge Phase

**Files:**
- All merge-phase files.

- [ ] **Step 1: Check all six registrations in dependency order**

Confirm P-MERGE Definitions/Correctness/Costs, followed by P-MERGE-SORT
Definitions/Correctness/Costs, with reader titles under Section 27.3.

- [ ] **Step 2: Run phase gates**

```bash
lake env lean Tests/Chapter_27_Interface.lean
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
lake env lean Tests/Chapter_27_Matrix_Interface.lean
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort -g '*.lean'
uv run python scripts/check_repository.py
git diff --check
```

Expected: all tests/checkers exit 0 and the unfinished-proof scan is empty.

- [ ] **Step 3: Confirm a clean phase checkpoint**

Run `git status --short`; expected output is empty.
