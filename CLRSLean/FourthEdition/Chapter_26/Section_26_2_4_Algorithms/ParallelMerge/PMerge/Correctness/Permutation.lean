import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.PMerge.Correctness.Boundaries

/-!
# CLRS Chapter 26.3 — P-MERGE Permutation Accounting

This module proves that the four recursive partitions and the midpoint pivot
reconstruct exactly the two normalized inputs.  The final normalization lemma
then transports this accounting back to the caller's original input order.
-/

namespace CLRS
namespace Chapter27
namespace ParallelMerge
namespace PMerge
namespace Correctness

variable [LinearOrder α]

/-- The secondary lower and upper partitions reconstruct the secondary input. -/
theorem secondary_reconstruct (S : MergeSplit α) :
    S.lowerSecondary ++ S.upperSecondary = S.secondary := by
  exact List.take_append_drop S.splitIndex S.secondary

/-- The normalized pair is either the original concatenation or its block swap. -/
theorem normalized_inputs_perm (S : MergeSplit α) :
    (S.primary ++ S.secondary).Perm (S.xs ++ S.ys) := by
  rcases S.inputOrder with h | h
  · simp [h.1, h.2]
  · simpa [h.1, h.2] using
      (List.perm_append_comm (l₁ := S.ys) (l₂ := S.xs))

/-- The lower partitions, pivot, and upper partitions are a permutation of
the normalized inputs. -/
theorem split_inputs_perm_normalized (S : MergeSplit α) :
    ((S.lowerPrimary ++ S.lowerSecondary) ++
      S.pivot :: (S.upperPrimary ++ S.upperSecondary)).Perm
      (S.primary ++ S.secondary) := by
  rw [← primary_reconstruct S, ← secondary_reconstruct S]
  have hswap := List.perm_append_comm
    (l₁ := S.lowerSecondary) (l₂ := S.pivot :: S.upperPrimary)
  simpa [List.append_assoc] using
    (hswap.append_left S.lowerPrimary).append_right S.upperSecondary

/-- Replacing both child partitions by arbitrary permutations preserves the
full original-input permutation. -/
theorem join_perm (S : MergeSplit α) {lowerOut upperOut : List α}
    (hlower : lowerOut.Perm (S.lowerPrimary ++ S.lowerSecondary))
    (hupper : upperOut.Perm (S.upperPrimary ++ S.upperSecondary)) :
    (lowerOut ++ S.pivot :: upperOut).Perm (S.xs ++ S.ys) := by
  exact (hlower.append (hupper.cons S.pivot)).trans
    ((split_inputs_perm_normalized S).trans (normalized_inputs_perm S))

end Correctness
end PMerge
end ParallelMerge
end Chapter27
end CLRS
