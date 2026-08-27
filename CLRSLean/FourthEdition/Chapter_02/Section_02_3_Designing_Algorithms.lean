import Mathlib
import CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.MergeSort

/-!
# CLRS Section 2.3 - Designing algorithms

This file introduces merge sort as the Chapter 2 divide-and-conquer example.
The executable top-level algorithm splits the input, recursively sorts both
halves, and invokes the locally verified, costed MERGE procedure at every
combine node.  A compatibility theorem identifies its output with Lean's
{lit}`List.mergeSort`.  Together these developments establish the algorithmic
contract:

* merge sort returns a sorted list;
* merge sort preserves the input elements.
* MERGE returns a sorted permutation of two sorted inputs;
* MERGE performs at most a linear number of head comparisons and writes each
  output element exactly once.
* the execution-derived merge-sort work satisfies the floor/ceiling recurrence
  and belongs to {lit}`Theta(n log n)` for all natural input lengths.

It also records the exact solution of the textbook recurrence on powers of two:
{lit}`T(1) = 1` and {lit}`T(2^(k+1)) = 2 * T(2^k) + 2^(k+1)`.

## Known simplifications

* The local MERGE uses immutable lists rather than temporary mutable arrays.
  Its counters charge head comparisons and output writes, not allocation or
  word-RAM instructions.

## Implementation details

* [Explicit MERGE](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/)
  ([definitions](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/Definitions/),
  [correctness](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/Correctness/),
  [cost](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/Cost/))
* [Executable merge sort](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/)
  ([definitions](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/Definitions/),
  [correctness](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/Correctness/),
  [cost](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/Cost/))
* [Merge-sort recurrence](CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge_Sort_Recurrence/)
-/

namespace CLRS
namespace Chapter02

/--
The merge-sort recurrence restricted to inputs of size {lit}`2^k`.

The index {lit}`k` represents the input length {lit}`2^k`; thus the successor equation is
the CLRS recurrence {lit}`T(2^(k+1)) = 2 * T(2^k) + 2^(k+1)` with unit base cost.
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
