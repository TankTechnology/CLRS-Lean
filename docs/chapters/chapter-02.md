# Chapter 2 - Getting Started

Chapter 2 is the first workflow pilot for `CLRS-Lean`.  The goal is not only to
formalize one algorithm, but to establish the repeatable loop we want to use for
the rest of CLRS:

```text
textbook section map
→ algorithm understanding
→ mathematical proof plan
→ Lean theorem interface
→ Lean proof
→ verification
→ proof-map update
```

## Section 2.1 - Insertion Sort

- Lean source: `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSort_sorted`
  - `CLRS.Chapter02.insertionSort_perm`

### Textbook Content

CLRS introduces insertion sort as the first concrete algorithm.  The textbook
version is array-based and is justified by a loop invariant: before each outer
loop iteration, the prefix already processed is sorted and contains exactly the
same elements as before.

### Algorithm Understanding

The Lean file uses a functional list version:

```lean
def insertSorted (x : Nat) : List Nat → List Nat
def insertionSort : List Nat → List Nat
```

This is the same algorithmic idea as the CLRS pseudocode: recursively sort the
tail, then insert the head into the sorted result.

### Mathematical Proof

The proof splits correctness into two facts:

1. `insertSorted` preserves orderedness.
2. `insertSorted` preserves elements up to permutation.

Then insertion sort follows by induction on the input list.

This corresponds to the CLRS loop invariant, but in a form that is more natural
for Lean:

```lean
theorem insertionSort_sorted (xs : List Nat) :
    Ordered (insertionSort xs)

theorem insertionSort_perm (xs : List Nat) :
    (insertionSort xs).Perm xs
```

### Lean Proof Notes

The section intentionally uses a small local predicate:

```lean
def Ordered : List Nat → Prop
```

This keeps the first Chapter 2 proof readable.  A later cleanup pass can compare
this with Mathlib's `List.Sorted` and decide whether to migrate.

## Section 2.2 - Analyzing Algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`
  - `CLRS.Chapter02.insertionSortWorstComparisons_eventually_quadratic`

This section introduces a lightweight chapter-level cost model.  Instead of
formalizing a full RAM machine, it records the usual insertion-sort worst-case
comparison count as a triangular sum and proves a quadratic upper bound:

```lean
def triangular : Nat → Nat

def insertionSortWorstComparisons (n : Nat) : Nat :=
  triangular (n - 1)
```

The public result is:

```lean
theorem insertionSortWorstComparisons_quadratic (n : Nat) :
    insertionSortWorstComparisons n ≤ n * n
```

The file also exposes a small eventual-bound predicate:

```lean
def EventuallyBoundedBy (f g : Nat → Nat) : Prop
```

This is enough for the first Chapter 2 pass.  A later complexity track can
replace it with a fuller RAM or cost-semantics model.

## Section 2.3 - Designing Algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.mergeSort_sortedLE`
  - `CLRS.Chapter02.mergeSort_perm`
  - `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`

This section introduces merge sort as the chapter's divide-and-conquer example.
For the first complete pass, the Lean file wraps Mathlib's verified
`List.mergeSort` implementation and exposes CLRS-facing theorem names:

```lean
def mergeSort (xs : List Nat) : List Nat

theorem mergeSort_sortedLE (xs : List Nat) :
    (mergeSort xs).SortedLE

theorem mergeSort_perm (xs : List Nat) :
    (mergeSort xs).Perm xs
```

This proves the main functional correctness contract: merge sort returns a
sorted list and preserves the input elements.

The file also formalizes the clean textbook recurrence on powers of two:

```lean
def mergeSortRecurrenceOnPowersOfTwo : Nat → Nat

theorem mergeSortRecurrenceOnPowersOfTwo_closedForm (k : Nat) :
    mergeSortRecurrenceOnPowersOfTwo k = (k + 1) * 2 ^ k
```

Here the index `k` represents input length `2^k`, with base case `T(1) = 1`
and recurrence `T(2^(k+1)) = 2 * T(2^k) + 2^(k+1)`.  This captures the core
`n log n` shape without forcing the first chapter pass to solve floors,
ceilings, or a full asymptotic library interface.

A later strengthening can inline the merge implementation and prove the
split/merge lemmas locally.

## What "Full RAM Semantics" Means

A full RAM semantics would formalize the textbook pseudocode as execution on a
small imperative machine.  Concretely, it would define machine states, arrays or
memory, variables/registers, control flow, a program counter or structured
statement semantics, primitive operations, and a cost assigned to each step.

That is stronger than the current Chapter 2 model.  The current model proves
mathematical algorithm contracts and selected cost recurrences.  A RAM model
would additionally prove that the exact CLRS-style imperative pseudocode runs
with the claimed line-by-line cost.

## Merge-Sort Complexity Scope

The power-of-two recurrence is Lean-formalized in Section 2.3, and so is the
fully general recurrence for every `n`, with
`T(n) = T(⌈n / 2⌉) + T(⌊n / 2⌋) + n`: `MergeSortRecurrence.theta_n_log_n_all_inputs`
proves the all-input Θ(n log n) bound for any monotone cost function satisfying
the recurrence, using floor/ceiling arithmetic and the Chapter 4.6 Master-theorem
sandwich bridge.

## Chapter 2 Completion Scope

This chapter is complete for the first `CLRS-Lean` pass over the main textbook
thread:

- Section 2.1: insertion sort correctness;
- Section 2.2: insertion-sort worst-case quadratic bound in a lightweight cost
  model;
- Section 2.3: merge sort correctness, the exact power-of-two recurrence
  solution, and the all-input Θ(n log n) recurrence bound.

Exercises, chapter-end problems, and a full RAM semantics are intentionally
future work.
