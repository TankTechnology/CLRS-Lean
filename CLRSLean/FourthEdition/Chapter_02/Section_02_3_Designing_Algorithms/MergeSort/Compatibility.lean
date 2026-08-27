import Mathlib

/-!
# CLRS Section 2.3 - Merge-sort compatibility API

The historical public {lit}`mergeSort` delegates to Mathlib.  The executable
Chapter 2 development proves its own recursion separately and connects to this
API through the unique sorted-permutation specification.
-/

namespace CLRS
namespace Chapter02

/-- Merge sort over natural numbers, using the standard nondecreasing order. -/
def mergeSort (xs : List Nat) : List Nat :=
  xs.mergeSort (· ≤ ·)

/-- Merge sort returns a list sorted in Mathlib's standard {lit}`SortedLE` sense. -/
theorem mergeSort_sortedLE (xs : List Nat) : (mergeSort xs).SortedLE := by
  simpa [mergeSort] using (List.sortedLE_mergeSort (l := xs))

/-- Merge sort preserves the input elements up to permutation. -/
theorem mergeSort_perm (xs : List Nat) : (mergeSort xs).Perm xs := by
  simpa [mergeSort] using (List.mergeSort_perm xs (· ≤ ·))

end Chapter02
end CLRS
