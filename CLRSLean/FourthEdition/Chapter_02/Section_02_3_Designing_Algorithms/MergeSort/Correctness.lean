import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.MergeSort.Definitions

/-!
# CLRS Section 2.3 - Merge-sort correctness

The recursive execution is proved to return the sorted permutation of its
input.  The proofs reuse the semantic contract of the exact {lit}`mergeWithCost`
call made by the program.
-/

namespace CLRS
namespace Chapter02

/-- The recursive costed merge-sort execution preserves every occurrence. -/
theorem mergeSortWithCost_perm (xs : List Nat) :
    (mergeSortWithCost xs).value.Perm xs := by
  refine WellFounded.induction (measure List.length).wf xs
    (C := fun ys => (mergeSortWithCost ys).value.Perm ys) ?_
  intro xs ih
  cases xs with
  | nil => simp [mergeSortWithCost.eq_def]
  | cons x tail =>
    cases tail with
    | nil => simp [mergeSortWithCost.eq_def]
    | cons y rest =>
      let input := x :: y :: rest
      let middle := input.length / 2
      let left := input.take middle
      let right := input.drop middle
      let leftRun := mergeSortWithCost left
      let rightRun := mergeSortWithCost right
      have hleftLength : left.length < input.length := by
        simp [left, middle, input]
        omega
      have hrightLength : right.length < input.length := by
        simp [right, middle, input]
        omega
      have ihLeft : leftRun.value.Perm left := by
        apply ih left
        change left.length < input.length
        exact hleftLength
      have ihRight : rightRun.value.Perm right := by
        apply ih right
        change right.length < input.length
        exact hrightLength
      have hmerge :
          (mergeWithCost leftRun.value rightRun.value).value.Perm
            (leftRun.value ++ rightRun.value) := by
        simpa [leftRun, rightRun, merge] using
          merge_perm leftRun.value rightRun.value
      have hhalves : (leftRun.value ++ rightRun.value).Perm (left ++ right) :=
        ihLeft.append ihRight
      have hsplit : left ++ right = input := by
        simp [left, right]
      rw [mergeSortWithCost.eq_def]
      dsimp only
      exact (hmerge.trans hhalves).trans (hsplit ▸ List.Perm.refl input)

/-- The recursive costed merge-sort execution returns nondecreasing output. -/
theorem mergeSortWithCost_sorted (xs : List Nat) :
    (mergeSortWithCost xs).value.SortedLE := by
  refine WellFounded.induction (measure List.length).wf xs
    (C := fun ys => (mergeSortWithCost ys).value.SortedLE) ?_
  intro xs ih
  cases xs with
  | nil =>
    rw [mergeSortWithCost.eq_def]
    exact List.sortedLE_iff_pairwise.mpr (by simp)
  | cons x tail =>
    cases tail with
    | nil =>
      rw [mergeSortWithCost.eq_def]
      exact List.sortedLE_iff_pairwise.mpr (by simp)
    | cons y rest =>
      let input := x :: y :: rest
      let middle := input.length / 2
      have hleftLength : (input.take middle).length < input.length := by
        simp [middle, input]
        omega
      have hrightLength : (input.drop middle).length < input.length := by
        simp [middle, input]
        omega
      have ihLeft : (mergeSortWithCost (input.take middle)).value.SortedLE := by
        apply ih (input.take middle)
        change (input.take middle).length < input.length
        exact hleftLength
      have ihRight : (mergeSortWithCost (input.drop middle)).value.SortedLE := by
        apply ih (input.drop middle)
        change (input.drop middle).length < input.length
        exact hrightLength
      rw [mergeSortWithCost.eq_def]
      dsimp only
      exact merge_sorted ihLeft ihRight

/-- The complete semantic contract of the executable merge sort. -/
theorem mergeSortWithCost_correct (xs : List Nat) :
    (mergeSortWithCost xs).value.SortedLE ∧
      (mergeSortWithCost xs).value.Perm xs :=
  ⟨mergeSortWithCost_sorted xs, mergeSortWithCost_perm xs⟩

/-- The costed execution erases to the historical public merge-sort value. -/
theorem mergeSortWithCost_eq_mergeSort (xs : List Nat) :
    (mergeSortWithCost xs).value = mergeSort xs := by
  have hperm : (mergeSortWithCost xs).value.Perm (mergeSort xs) :=
    (mergeSortWithCost_perm xs).trans (mergeSort_perm xs).symm
  exact hperm.eq_of_sortedLE (mergeSortWithCost_sorted xs) (mergeSort_sortedLE xs)

/-- Value-only erasure of the costed execution. -/
theorem mergeSortValue_eq (xs : List Nat) :
    mergeSortValue xs = (mergeSortWithCost xs).value := rfl

end Chapter02
end CLRS
