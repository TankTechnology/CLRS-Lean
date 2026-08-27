# Executable Costed Merge Sort Design

## Goal

Close the Chapter 2 semantic bridge between the locally verified `MERGE`
procedure and the public merge-sort theorem.  The new execution must perform
the textbook split--recurse--merge control flow, call `mergeWithCost` at every
combine node, and expose correctness and cost facts about that same execution.

## Boundary

The development models immutable lists, head comparisons, and output writes.
It does not claim mutable temporary arrays, allocation cost, or word-RAM
semantics.  Those are outside the repository's current Chapter 2 boundary.

The existing `mergeSort` wrapper around Mathlib remains as a compatibility API.
The new execution is connected to it extensionally through the common
specification "sorted permutation of the input"; no implementation equality
with Mathlib's internal merge-sort recursion is assumed.

## Module structure

Keep the proof surface small and avoid a new large Section 2.3 file:

- `MergeSort/Definitions.lean`: execution record, terminating recursive
  split--recurse--`mergeWithCost` program, and value/cost projections.
- `MergeSort/Correctness.lean`: split facts, permutation preservation,
  sortedness, and public specification/compatibility theorems.
- `MergeSort/Cost.lean`: exact combine-cost equation, length invariance of the
  extracted work function, recurrence, and asymptotic theorem.
- `MergeSort.lean`: stable facade.

`Merge_Sort_Recurrence.lean` currently imports the Section 2.3 facade only for
documentation.  Remove that dependency so `MergeSort/Cost.lean` can reuse its
general all-input recurrence theorem without creating an import cycle.

## Execution model

`MergeSortExecution` records:

- `value`: returned list;
- `comparisons`: sum of actual `mergeWithCost` head comparisons;
- `outputWrites`: sum of actual `mergeWithCost` output writes;
- `work`: one unit at a singleton leaf plus the output writes charged at every
  combine node.

The recursive definition has three cases: empty, singleton, and at least two
elements.  In the recursive case it splits at `length / 2`, recursively runs
both halves, and calls `mergeWithCost leftRun.value rightRun.value`.  Termination
is by input length; both halves are strictly shorter in the two-or-more case.

The `work` counter deliberately follows the execution.  It is not defined as
the already-known merge-sort recurrence.  A later theorem derives that
recurrence from the program and `merge_outputWrites_eq`.

## Public theorem surface

The strong truth-source theorems are:

```lean
theorem mergeSortWithCost_perm (xs : List Nat) :
    (mergeSortWithCost xs).value.Perm xs

theorem mergeSortWithCost_sorted (xs : List Nat) :
    (mergeSortWithCost xs).value.SortedLE

theorem mergeSortWithCost_correct (xs : List Nat) :
    (mergeSortWithCost xs).value.SortedLE ∧
      (mergeSortWithCost xs).value.Perm xs

theorem mergeSortWithCost_eq_mergeSort (xs : List Nat) :
    (mergeSortWithCost xs).value = mergeSort xs
```

The last theorem uses sorted-permutation uniqueness for a linear order; it is
an erasure/specification bridge, not a claim that Mathlib uses the same code.

The cost layer exposes an exact recursive equation for every input with at
least two elements and then a length-indexed extracted function:

```lean
def mergeSortWork (n : Nat) : Nat :=
  (mergeSortWithCost (List.replicate n 0)).work

theorem mergeSortWithCost_work_eq_length (xs : List Nat) :
    (mergeSortWithCost xs).work = mergeSortWork xs.length

theorem mergeSortWork_recurrence :
    MergeSortRecurrence.Recurrence (fun n => (mergeSortWork n : Real))

theorem mergeSortWork_isBigTheta_nlogn :
    Chapter03.isBigTheta (fun n => (mergeSortWork n : Real))
      (fun n => (n : Real) * Real.log n)
```

If the exact monotonicity lemma needed by the reusable all-input theorem is
substantially harder than the recurrence itself, it remains a named private
lemma in `Cost.lean`; the public asymptotic theorem may not add monotonicity as
an unproved assumption.

## Proof strategy

Correctness follows strong recursion over input length.  The induction
hypotheses apply to `take (length / 2)` and `drop (length / 2)`.  `List.Perm`
composition uses the split identity `take ++ drop = xs`, and the combine step
uses the already proved `merge_perm` and `merge_sorted`.

Cost attachment follows the same recursion.  The crucial local equality is
`merge_outputWrites_eq`; after rewriting recursive output lengths with the
permutation theorems, the combine charge is exactly `xs.length`.  This also
shows that `work` is input-value independent and permits extraction of
`mergeSortWork`.

The recurrence theorem is then passed to the existing Chapter 2/4 all-input
bridge.  No asymptotic theorem is accepted unless its cost function is proved
equal to the execution's counter.

## Verification

Development begins with failing `#check`s in
`Tests/Chapter_02_Merge_Interface.lean`.  Only the affected modules and focused
test are built during proof development.  The chapter trust file receives
native axiom checks before the final repository gate.

