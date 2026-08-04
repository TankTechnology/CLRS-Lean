import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Definitions

/-!
# CLRS Chapter 27.3 — P-MERGE Order Boundaries

This module isolates the order facts behind one P-MERGE split.  In
particular, lower bound puts every duplicate of the pivot on the upper side,
so the lower secondary partition is strictly below the pivot while the upper
partition is greater than or equal to it.
-/

namespace CLRS
namespace Chapter27

/-- The semantic result of merging two sorted lists. -/
structure PMergeSpec [LinearOrder α] (xs ys out : List α) : Prop where
  sorted : out.Pairwise (· ≤ ·)
  perm : out.Perm (xs ++ ys)
  length_eq : out.length = xs.length + ys.length

namespace ParallelMerge
namespace PMerge
namespace Correctness

variable [LinearOrder α]

/-- Normalization preserves sortedness of the primary input. -/
theorem primary_sorted (S : MergeSplit α)
    (hxs : S.xs.Pairwise (· ≤ ·)) (hys : S.ys.Pairwise (· ≤ ·)) :
    S.primary.Pairwise (· ≤ ·) := by
  rcases S.inputOrder with h | h
  · simpa [h.1] using hxs
  · simpa [h.1] using hys

/-- Normalization preserves sortedness of the secondary input. -/
theorem secondary_sorted (S : MergeSplit α)
    (hxs : S.xs.Pairwise (· ≤ ·)) (hys : S.ys.Pairwise (· ≤ ·)) :
    S.secondary.Pairwise (· ≤ ·) := by
  rcases S.inputOrder with h | h
  · simpa [h.2] using hys
  · simpa [h.2] using hxs

/-- Taking the lower primary partition preserves sortedness. -/
theorem lowerPrimary_sorted (S : MergeSplit α)
    (hprimary : S.primary.Pairwise (· ≤ ·)) :
    S.lowerPrimary.Pairwise (· ≤ ·) := by
  exact hprimary.take

/-- Dropping the pivot and the lower prefix preserves primary sortedness. -/
theorem upperPrimary_sorted (S : MergeSplit α)
    (hprimary : S.primary.Pairwise (· ≤ ·)) :
    S.upperPrimary.Pairwise (· ≤ ·) := by
  exact hprimary.drop

/-- Taking the binary-search prefix preserves secondary sortedness. -/
theorem lowerSecondary_sorted (S : MergeSplit α)
    (hsecondary : S.secondary.Pairwise (· ≤ ·)) :
    S.lowerSecondary.Pairwise (· ≤ ·) := by
  exact hsecondary.take

/-- Dropping the binary-search prefix preserves secondary sortedness. -/
theorem upperSecondary_sorted (S : MergeSplit α)
    (hsecondary : S.secondary.Pairwise (· ≤ ·)) :
    S.upperSecondary.Pairwise (· ≤ ·) := by
  exact hsecondary.drop

/-- The primary input is its lower prefix, pivot, and upper suffix. -/
theorem primary_reconstruct (S : MergeSplit α) :
    S.lowerPrimary ++ S.pivot :: S.upperPrimary = S.primary := by
  have hi : S.pivotIndex < S.primary.length := by
    simpa [MergeSplit.pivotIndex] using S.pivotIndex_lt
  have hpivot : S.primary.get ⟨S.pivotIndex, hi⟩ = S.pivot := by
    simpa [MergeSplit.pivotIndex] using S.pivot_eq
  simp only [MergeSplit.lowerPrimary, MergeSplit.upperPrimary]
  rw [← hpivot, List.cons_get_drop_succ, List.take_append_drop]

/-- Every element in the primary lower partition is at most the pivot. -/
theorem lowerPrimary_le_pivot (S : MergeSplit α)
    (hprimary : S.primary.Pairwise (· ≤ ·)) :
    ∀ x ∈ S.lowerPrimary, x ≤ S.pivot := by
  have hsplit :
      (S.lowerPrimary ++ S.pivot :: S.upperPrimary).Pairwise (· ≤ ·) := by
    rw [primary_reconstruct S]
    exact hprimary
  have hcross := (List.pairwise_append.mp hsplit).2.2
  intro x hx
  exact hcross x hx S.pivot (by simp)

/-- Every element in the primary upper partition is at least the pivot. -/
theorem pivot_le_upperPrimary (S : MergeSplit α)
    (hprimary : S.primary.Pairwise (· ≤ ·)) :
    ∀ x ∈ S.upperPrimary, S.pivot ≤ x := by
  have hsplit :
      (S.lowerPrimary ++ S.pivot :: S.upperPrimary).Pairwise (· ≤ ·) := by
    rw [primary_reconstruct S]
    exact hprimary
  have htail := (List.pairwise_append.mp hsplit).2.1
  simpa using (List.pairwise_cons.mp htail).1

/-- Binary lower bound gives the duplicate-sensitive secondary partition. -/
theorem secondary_partition (S : MergeSplit α)
    (hsecondary : S.secondary.Pairwise (· ≤ ·)) :
    LowerBoundSpec S.secondary S.pivot S.splitIndex := by
  rw [MergeSplit.splitIndex, S.search_eq]
  exact binaryLowerBound_partition S.secondary S.pivot hsecondary

/-- Every element in the lower secondary partition is at most the pivot.

The binary-search theorem is stronger: these elements are strictly below the
pivot.  Weakening here is exactly what the sorted join needs.
-/
theorem lowerSecondary_le_pivot (S : MergeSplit α)
    (hsecondary : S.secondary.Pairwise (· ≤ ·)) :
    ∀ x ∈ S.lowerSecondary, x ≤ S.pivot := by
  intro x hx
  exact (secondary_partition S hsecondary).left_lt x hx |>.le

/-- Every element in the upper secondary partition is at least the pivot. -/
theorem pivot_le_upperSecondary (S : MergeSplit α)
    (hsecondary : S.secondary.Pairwise (· ≤ ·)) :
    ∀ x ∈ S.upperSecondary, S.pivot ≤ x := by
  exact (secondary_partition S hsecondary).right_ge

/-- A permutation of the two lower partitions remains bounded by the pivot. -/
theorem lower_output_le_pivot (S : MergeSplit α) {out : List α}
    (hprimary : S.primary.Pairwise (· ≤ ·))
    (hsecondary : S.secondary.Pairwise (· ≤ ·))
    (hout : out.Perm (S.lowerPrimary ++ S.lowerSecondary)) :
    ∀ x ∈ out, x ≤ S.pivot := by
  intro x hx
  have hx' := hout.mem_iff.mp hx
  rcases List.mem_append.mp hx' with hxPrimary | hxSecondary
  · exact lowerPrimary_le_pivot S hprimary x hxPrimary
  · exact lowerSecondary_le_pivot S hsecondary x hxSecondary

/-- A permutation of the two upper partitions remains above the pivot. -/
theorem pivot_le_upper_output (S : MergeSplit α) {out : List α}
    (hprimary : S.primary.Pairwise (· ≤ ·))
    (hsecondary : S.secondary.Pairwise (· ≤ ·))
    (hout : out.Perm (S.upperPrimary ++ S.upperSecondary)) :
    ∀ x ∈ out, S.pivot ≤ x := by
  intro x hx
  have hx' := hout.mem_iff.mp hx
  rcases List.mem_append.mp hx' with hxPrimary | hxSecondary
  · exact pivot_le_upperPrimary S hprimary x hxPrimary
  · exact pivot_le_upperSecondary S hsecondary x hxSecondary

/-- Sorted recursive results join around the pivot into a sorted result. -/
theorem join_sorted (S : MergeSplit α) {lowerOut upperOut : List α}
    (hprimary : S.primary.Pairwise (· ≤ ·))
    (hsecondary : S.secondary.Pairwise (· ≤ ·))
    (hlower : PMergeSpec S.lowerPrimary S.lowerSecondary lowerOut)
    (hupper : PMergeSpec S.upperPrimary S.upperSecondary upperOut) :
    (lowerOut ++ S.pivot :: upperOut).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨hlower.sorted, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    exact ⟨pivot_le_upper_output S hprimary hsecondary hupper.perm, hupper.sorted⟩
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lower_output_le_pivot S hprimary hsecondary hlower.perm x hx
    · exact le_trans
        (lower_output_le_pivot S hprimary hsecondary hlower.perm x hx)
        (pivot_le_upper_output S hprimary hsecondary hupper.perm y hy)

end Correctness
end PMerge
end ParallelMerge
end Chapter27
end CLRS
