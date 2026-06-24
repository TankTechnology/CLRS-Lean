import Mathlib
import CLRSLean.Chapter_02.Section_02_1_Insertion_Sort

/-!
# CLRS Section 2.3 - Designing algorithms

This file introduces merge sort as the Chapter 2 divide-and-conquer example.
For this first complete chapter pass, we use Lean's verified List.mergeSort
implementation and expose CLRS-facing theorem names.  This keeps the chapter
workflow focused on the algorithmic contract:

* merge sort returns a sorted list;
* merge sort preserves the input elements.

It also records the exact solution of the textbook recurrence on powers of two:
`T(1) = 1` and `T(2^(k+1)) = 2 * T(2^k) + 2^(k+1)`.

A later strengthening can inline the merge routine and prove the split/merge
lemmas locally if we want a from-scratch artifact.
-/

namespace CLRS
namespace Chapter02

/-- Merge sort over natural numbers, using the standard nondecreasing order. -/
def mergeSort (xs : List Nat) : List Nat :=
  xs.mergeSort (· ≤ ·)

/-- Merge sort returns a list sorted in Mathlib's standard `SortedLE` sense. -/
theorem mergeSort_sortedLE (xs : List Nat) : (mergeSort xs).SortedLE := by
  simpa [mergeSort] using (List.sortedLE_mergeSort (l := xs))

/-- Merge sort preserves the input elements up to permutation. -/
theorem mergeSort_perm (xs : List Nat) : (mergeSort xs).Perm xs := by
  simpa [mergeSort] using (List.mergeSort_perm xs (· ≤ ·))

/--
The merge-sort recurrence restricted to inputs of size `2^k`.

The index `k` represents the input length `2^k`; thus the successor equation is
the CLRS recurrence `T(2^(k+1)) = 2 * T(2^k) + 2^(k+1)` with unit base cost.
-/
def mergeSortRecurrenceOnPowersOfTwo : Nat → Nat
  | 0 => 1
  | k + 1 => 2 * mergeSortRecurrenceOnPowersOfTwo k + 2 ^ (k + 1)

/-- The exact closed form for the power-of-two merge-sort recurrence. -/
theorem mergeSortRecurrenceOnPowersOfTwo_closedForm (k : Nat) :
    mergeSortRecurrenceOnPowersOfTwo k = (k + 1) * 2 ^ k := by
  induction k with
  | zero =>
      simp [mergeSortRecurrenceOnPowersOfTwo]
  | succ k ih =>
      calc
        mergeSortRecurrenceOnPowersOfTwo (k + 1)
            = 2 * ((k + 1) * 2 ^ k) + 2 ^ (k + 1) := by
                simp [mergeSortRecurrenceOnPowersOfTwo, ih]
        _ = (k + 2) * 2 ^ (k + 1) := by
                rw [Nat.pow_succ]
                let p := 2 ^ k
                have hmul : 2 * ((k + 1) * p) = (k + 1) * (p * 2) := by
                  rw [← Nat.mul_assoc]
                  rw [Nat.mul_comm 2 (k + 1)]
                  rw [Nat.mul_assoc]
                  rw [Nat.mul_comm 2 p]
                calc
                  2 * ((k + 1) * p) + p * 2 = (k + 1) * (p * 2) + p * 2 := by
                    rw [hmul]
                  _ = ((k + 1) + 1) * (p * 2) := by
                    simpa using (Nat.add_mul (k + 1) 1 (p * 2)).symm
                  _ = (k + 2) * (p * 2) := by
                    simp [Nat.add_assoc]

end Chapter02
end CLRS
