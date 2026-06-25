import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import Mathlib

/-!
# CLRS Section 7.2 - Performance of quicksort

This section defines a deterministic comparison-count cost model for the
first-pivot functional quicksort from Section 7.1 and proves a quadratic upper
bound: on any list of length `n`, quicksort performs at most `n²` comparisons.

The cost model mirrors the fuelled recursion of `quickSortFuel`: each non-empty
call compares every tail element against the pivot (one comparison each) and then
adds the recursive comparison counts for the left and right partitions.

Main results:

- Lemma `partitionAround_length_add`: the two partition halves together have
  exactly the length of the scanned tail.
- Theorem `quickSortComparisons_quadratic`: for any list `xs`,
  `quickSortComparisons xs ≤ xs.length * xs.length`.

Notation conventions:

- `partitionAround p xs` : the stable partition from Section 7.1
- `quickSortComparisonsFuel fuel xs` : fuelled comparison counter
- `quickSortComparisons xs` : total comparison count with full fuel
-/

namespace CLRS
namespace Chapter07

open Chapter07

/-! ## Comparison-count cost model -/

/--
Fuelled comparison counter that mirrors the recursion structure of
`quickSortFuel`.

Each non-empty call adds `xs.length` comparisons (one per tail element tested
against the pivot) to the recursive comparison counts for the left and right
partition halves.
-/
def quickSortComparisonsFuel : Nat → List Nat → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, pivot :: xs =>
      let parts := partitionAround pivot xs
      xs.length + quickSortComparisonsFuel fuel parts.1 +
        quickSortComparisonsFuel fuel parts.2

/--
Total number of comparisons performed by functional quicksort on a list.

Uses exactly `xs.length` fuel, matching the public `quickSort` definition so that
`quickSortComparisons xs` counts the comparisons in `quickSort xs`.
-/
def quickSortComparisons (xs : List Nat) : Nat :=
  quickSortComparisonsFuel xs.length xs

/-! ## Partition length conservation -/

/--
The two halves of a pivot partition together contain every element of the
scanned tail.  This is an immediate consequence of
`partitionAround_perm`.
-/
theorem partitionAround_length_add (p : Nat) (xs : List Nat) :
    (partitionAround p xs).1.length + (partitionAround p xs).2.length = xs.length := by
  have hperm := partitionAround_perm p xs
  have hlen := hperm.length_eq
  simpa [List.length_append] using hlen

/-! ## Quadratic upper bound -/

/--
When the fuel is at least the list length, the comparison count of quicksort is
bounded by the square of the list length.

The proof mimics the fuel induction in `quickSortFuel_perm`: the left and right
partition lengths are bounded by the tail length, and the inductive hypotheses
give `≤ a²` and `≤ b²` bounds.  A `nlinarith` step then closes the algebraic
gap `(a+b) + a² + b² ≤ (a+b+1)²`.
-/
theorem quickSortComparisonsFuel_quadratic :
    ∀ (fuel : Nat) (xs : List Nat), xs.length ≤ fuel →
      quickSortComparisonsFuel fuel xs ≤ xs.length * xs.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen
      have hnil : xs = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      simp [quickSortComparisonsFuel, hnil]
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil =>
          simp [quickSortComparisonsFuel]
      | cons pivot tail =>
          let parts := partitionAround pivot tail
          have htail_len : tail.length ≤ fuel := by
            exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
          have hleft_len : parts.1.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_left_length_le pivot tail) htail_len
          have hright_len : parts.2.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_right_length_le pivot tail) htail_len
          have hleft_bound : quickSortComparisonsFuel fuel parts.1 ≤
              parts.1.length * parts.1.length :=
            ih parts.1 hleft_len
          have hright_bound : quickSortComparisonsFuel fuel parts.2 ≤
              parts.2.length * parts.2.length :=
            ih parts.2 hright_len
          have hparts_len : parts.1.length + parts.2.length = tail.length :=
            partitionAround_length_add pivot tail
          simp [quickSortComparisonsFuel]
          have hgoal : tail.length + quickSortComparisonsFuel fuel parts.1 +
              quickSortComparisonsFuel fuel parts.2 ≤
              (tail.length + 1) * (tail.length + 1) := by
            nlinarith
          exact hgoal

/--
**Quadratic upper bound for quicksort comparisons.**  On any list `xs` of length
`n`, functional first-pivot quicksort performs at most `n²` comparisons.

This corresponds to the deterministic worst-case analysis in CLRS Section 7.2.
-/
theorem quickSortComparisons_quadratic (xs : List Nat) :
    quickSortComparisons xs ≤ xs.length * xs.length := by
  unfold quickSortComparisons
  exact quickSortComparisonsFuel_quadratic xs.length xs (Nat.le_refl _)

end Chapter07
end CLRS
