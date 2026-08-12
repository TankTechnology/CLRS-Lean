import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.PMerge.Correctness.Permutation

/-!
# CLRS Chapter 26.3 — P-MERGE Correctness

P-MERGE is proved correct by strong induction on the sum of the input lengths.
The induction follows the algorithm's actual midpoint/lower-bound split: both
recursive problems are strictly smaller because the primary pivot is removed.

Main results:

* {lit}`pMerge_correct`: sortedness, permutation, and exact output length.
* {lit}`pMerge_value_sorted`, {lit}`pMerge_value_perm`, and
  {lit}`pMerge_value_length`: direct projections for downstream proofs.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMerge
namespace PMerge
namespace Correctness

variable [LinearOrder α]

/-- The value projection of a nonempty P-MERGE call is the two recursive
values joined around the chosen pivot. -/
theorem value_eq_join (xs ys : List α)
    (hzero : xs.length + ys.length ≠ 0) :
    let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
    (pMerge xs ys).value =
      (pMerge S.lowerPrimary S.lowerSecondary).value ++
        S.pivot :: (pMerge S.upperPrimary S.upperSecondary).value := by
  have hnotNil : ¬ (xs = [] ∧ ys = []) := by
    rintro ⟨rfl, rfl⟩
    exact hzero rfl
  rw [pMerge]
  simp [hnotNil]

/-- Strong-induction form of P-MERGE correctness, indexed by total input size. -/
private theorem correct_of_total (n : ℕ) :
    ∀ (xs ys : List α),
      xs.length + ys.length = n →
      xs.Pairwise (· ≤ ·) →
      ys.Pairwise (· ≤ ·) →
      PMergeSpec xs ys (pMerge xs ys).value := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs ys htotal hxs hys
      by_cases hzero : xs.length + ys.length = 0
      · have hxsNil : xs = [] := by
          simpa using (show xs.length = 0 by omega)
        have hysNil : ys = [] := by
          simpa using (show ys.length = 0 by omega)
        subst xs
        subst ys
        have hvalue : (pMerge ([] : List α) []).value = [] := by
          simp [pMerge]
        rw [hvalue]
        exact ⟨List.Pairwise.nil, List.Perm.refl [], rfl⟩
      · let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
        have hSxs : S.xs.Pairwise (· ≤ ·) := by
          simpa [S] using hxs
        have hSys : S.ys.Pairwise (· ≤ ·) := by
          simpa [S] using hys
        have hprimary := primary_sorted S hSxs hSys
        have hsecondary := secondary_sorted S hSxs hSys
        have hleft_lt : S.leftSize < n := by
          calc
            S.leftSize < S.totalSize := S.leftSize_lt
            _ = xs.length + ys.length := by
              simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hright_lt : S.rightSize < n := by
          calc
            S.rightSize < S.totalSize := S.rightSize_lt
            _ = xs.length + ys.length := by
              simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hlower : PMergeSpec S.lowerPrimary S.lowerSecondary
            (pMerge S.lowerPrimary S.lowerSecondary).value :=
          ih S.leftSize hleft_lt S.lowerPrimary S.lowerSecondary rfl
            (lowerPrimary_sorted S hprimary)
            (lowerSecondary_sorted S hsecondary)
        have hupper : PMergeSpec S.upperPrimary S.upperSecondary
            (pMerge S.upperPrimary S.upperSecondary).value :=
          ih S.rightSize hright_lt S.upperPrimary S.upperSecondary rfl
            (upperPrimary_sorted S hprimary)
            (upperSecondary_sorted S hsecondary)
        have hsorted := join_sorted S hprimary hsecondary hlower hupper
        have hperm := join_perm S hlower.perm hupper.perm
        have hjoined : PMergeSpec S.xs S.ys
            ((pMerge S.lowerPrimary S.lowerSecondary).value ++
              S.pivot :: (pMerge S.upperPrimary S.upperSecondary).value) := by
          refine ⟨hsorted, hperm, ?_⟩
          simpa using hperm.length_eq
        have hvalue : (pMerge xs ys).value =
            (pMerge S.lowerPrimary S.lowerSecondary).value ++
              S.pivot :: (pMerge S.upperPrimary S.upperSecondary).value := by
          simpa [S] using value_eq_join xs ys hzero
        rw [hvalue]
        simpa [S] using hjoined

end Correctness
end PMerge
end ParallelMerge

/-! ## Public theorems -/

/-- P-MERGE returns a sorted permutation of its two sorted inputs, with exact
output length. -/
theorem pMerge_correct [LinearOrder α] (xs ys : List α)
    (hxs : xs.Pairwise (· ≤ ·)) (hys : ys.Pairwise (· ≤ ·)) :
    PMergeSpec xs ys (pMerge xs ys).value := by
  exact ParallelMerge.PMerge.Correctness.correct_of_total
    (xs.length + ys.length) xs ys rfl hxs hys

/-- The value returned by P-MERGE is sorted. -/
theorem pMerge_value_sorted [LinearOrder α] (xs ys : List α)
    (hxs : xs.Pairwise (· ≤ ·)) (hys : ys.Pairwise (· ≤ ·)) :
    (pMerge xs ys).value.Pairwise (· ≤ ·) :=
  (pMerge_correct xs ys hxs hys).sorted

/-- The value returned by P-MERGE contains exactly the two input multisets. -/
theorem pMerge_value_perm [LinearOrder α] (xs ys : List α)
    (hxs : xs.Pairwise (· ≤ ·)) (hys : ys.Pairwise (· ≤ ·)) :
    (pMerge xs ys).value.Perm (xs ++ ys) :=
  (pMerge_correct xs ys hxs hys).perm

/-- P-MERGE's value has exactly the sum of the two input lengths. -/
theorem pMerge_value_length [LinearOrder α] (xs ys : List α)
    (hxs : xs.Pairwise (· ≤ ·)) (hys : ys.Pairwise (· ≤ ·)) :
    (pMerge xs ys).value.length = xs.length + ys.length :=
  (pMerge_correct xs ys hxs hys).length_eq

end Chapter27
end CLRS
