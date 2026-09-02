import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMergeSort.Correctness.Spec
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.PMerge.Correctness

/-!
# CLRS Chapter 26.3 — P-MERGE-SORT Correctness

P-MERGE-SORT is proved correct by strong induction on the input length.  The
recursive case sorts the midpoint halves, invokes the already proved P-MERGE
specification, and reconstructs the original input through take/drop.

Main results:

* {lit}`pMergeSort_correct`: sortedness, permutation, and exact output length.
* {lit}`pMergeSort_value_sorted`, {lit}`pMergeSort_value_perm`, and
  {lit}`pMergeSort_value_length`: direct projections for downstream proofs.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMergeSort
namespace Correctness

variable [LinearOrder α]

/-- Strong-induction form of P-MERGE-SORT correctness, indexed by input
length. -/
private theorem correct_of_length (n : ℕ) :
    ∀ (xs : List α), xs.length = n →
      PMergeSortSpec xs (pMergeSort xs).value := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs hlength
      by_cases hsmall : xs.length ≤ 1
      · have hvalue := value_eq_self xs hsmall
        rw [hvalue]
        exact ⟨pairwise_of_length_le_one xs hsmall, List.Perm.refl xs, rfl⟩
      · let mid := xs.length / 2
        let left := xs.take mid
        let right := xs.drop mid
        have hn : 2 ≤ n := by omega
        have hleftLength : left.length = mid := by
          simp [left, mid]
          omega
        have hleft_lt : left.length < n := by
          rw [hleftLength]
          simp [mid]
          omega
        have hrightLength : right.length = xs.length - mid := by
          simp [right]
        have hright_lt : right.length < n := by
          rw [hrightLength]
          simp [mid]
          omega
        have hleft : PMergeSortSpec left (pMergeSort left).value :=
          ih left.length hleft_lt left rfl
        have hright : PMergeSortSpec right (pMergeSort right).value :=
          ih right.length hright_lt right rfl
        have hmerge : PMergeSpec (pMergeSort left).value (pMergeSort right).value
            (pMerge (pMergeSort left).value (pMergeSort right).value).value :=
          pMerge_correct _ _ hleft.sorted hright.sorted
        have hvalue : (pMergeSort xs).value =
            (pMerge (pMergeSort left).value (pMergeSort right).value).value := by
          simpa [mid, left, right] using value_eq_merge xs hsmall
        have hperm :
            (pMerge (pMergeSort left).value (pMergeSort right).value).value.Perm xs := by
          have hparts : ((pMergeSort left).value ++
              (pMergeSort right).value).Perm (left ++ right) :=
            hleft.perm.append hright.perm
          have htakeDrop : left ++ right = xs := by
            simp [left, right]
          rw [htakeDrop] at hparts
          exact hmerge.perm.trans hparts
        rw [hvalue]
        exact ⟨hmerge.sorted, hperm, hperm.length_eq⟩

end Correctness
end ParallelMergeSort

/-! ## Public theorems -/

/-- P-MERGE-SORT returns a sorted permutation of every input list, with exact
output length. -/
theorem pMergeSort_correct [LinearOrder α] (xs : List α) :
    PMergeSortSpec xs (pMergeSort xs).value := by
  exact ParallelMergeSort.Correctness.correct_of_length xs.length xs rfl

/-- The value returned by P-MERGE-SORT is sorted. -/
theorem pMergeSort_value_sorted [LinearOrder α] (xs : List α) :
    (pMergeSort xs).value.Pairwise (· ≤ ·) :=
  (pMergeSort_correct xs).sorted

/-- The value returned by P-MERGE-SORT contains exactly the input multiset. -/
theorem pMergeSort_value_perm [LinearOrder α] (xs : List α) :
    (pMergeSort xs).value.Perm xs :=
  (pMergeSort_correct xs).perm

/-- P-MERGE-SORT's value has exactly the input length. -/
theorem pMergeSort_value_length [LinearOrder α] (xs : List α) :
    (pMergeSort xs).value.length = xs.length :=
  (pMergeSort_correct xs).length_eq

end Chapter27
end CLRS
