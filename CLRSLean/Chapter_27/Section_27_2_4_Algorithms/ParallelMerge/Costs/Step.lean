import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Structure
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound.Costs

/-!
# CLRS Chapter 27.3 — One P-MERGE Cost Step

These reader theorems unfold one nonempty executable P-MERGE call.  They keep
the actual normalized split visible so later strong-induction proofs can use
the exact child sizes and the three-quarter shrink theorem.
-/

namespace CLRS
namespace Chapter27

/-- Exact work of one nonempty P-MERGE step: sequential search, two recursive
children, one parallel fork/join, and one pivot-placement operation. -/
theorem pMerge_work_step_eq [LinearOrder α] (xs ys : List α)
    (hzero : xs.length + ys.length ≠ 0) :
    let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
    (pMerge xs ys).work =
      S.search.work +
        (pMerge S.lowerPrimary S.lowerSecondary).work +
        (pMerge S.upperPrimary S.upperSecondary).work + 2 := by
  rw [pMerge]
  simp only [hzero, ↓reduceDIte]
  simp [Costed.seq_work, Costed.par_work, Costed.charge_work]
  omega

/-- Exact span of one nonempty P-MERGE step.  Binary search precedes the slower
recursive child; fork/join and pivot placement contribute two more units. -/
theorem pMerge_span_step_eq [LinearOrder α] (xs ys : List α)
    (hzero : xs.length + ys.length ≠ 0) :
    let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
    (pMerge xs ys).span =
      S.search.span +
        max (pMerge S.lowerPrimary S.lowerSecondary).span
          (pMerge S.upperPrimary S.upperSecondary).span + 2 := by
  rw [pMerge]
  simp only [hzero, ↓reduceDIte]
  simp [Costed.seq_span, Costed.par_span, Costed.charge_span]
  omega

private theorem split_search_work_le_total_log [LinearOrder α]
    (S : MergeSplit α) :
    S.search.work ≤ Nat.log 2 S.totalSize + 1 := by
  have hsearch :
      S.search.work ≤ Nat.log 2 S.secondary.length + 1 := by
    rw [S.search_eq]
    exact binaryLowerBound_work_le_log S.secondary S.pivot
  have hsecondary : S.secondary.length ≤ S.totalSize := by
    calc
      S.secondary.length ≤ S.primary.length + S.secondary.length := Nat.le_add_left _ _
      _ = S.totalSize := by
        simpa [MergeSplit.totalSize] using S.normalized_total
  have hlog : Nat.log 2 S.secondary.length ≤ Nat.log 2 S.totalSize :=
    Nat.log_monotone hsecondary
  omega

private theorem split_search_span_le_total_log [LinearOrder α]
    (S : MergeSplit α) :
    S.search.span ≤ Nat.log 2 S.totalSize + 1 := by
  have hsearch :
      S.search.span ≤ Nat.log 2 S.secondary.length + 1 := by
    rw [S.search_eq]
    exact binaryLowerBound_span_le_log S.secondary S.pivot
  have hsecondary : S.secondary.length ≤ S.totalSize := by
    calc
      S.secondary.length ≤ S.primary.length + S.secondary.length := Nat.le_add_left _ _
      _ = S.totalSize := by
        simpa [MergeSplit.totalSize] using S.normalized_total
  have hlog : Nat.log 2 S.secondary.length ≤ Nat.log 2 S.totalSize :=
    Nat.log_monotone hsecondary
  omega

/-- One-step work upper bound in a form suitable for strong induction. -/
theorem pMerge_work_step_le [LinearOrder α] (xs ys : List α)
    (hzero : xs.length + ys.length ≠ 0) :
    let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
    (pMerge xs ys).work ≤
      (pMerge S.lowerPrimary S.lowerSecondary).work +
        (pMerge S.upperPrimary S.upperSecondary).work +
        Nat.log 2 S.totalSize + 3 := by
  dsimp only
  let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
  have heq := pMerge_work_step_eq xs ys hzero
  have hsearch := split_search_work_le_total_log S
  change (pMerge xs ys).work ≤
    (pMerge S.lowerPrimary S.lowerSecondary).work +
      (pMerge S.upperPrimary S.upperSecondary).work +
      Nat.log 2 S.totalSize + 3
  change (pMerge xs ys).work = S.search.work +
    (pMerge S.lowerPrimary S.lowerSecondary).work +
    (pMerge S.upperPrimary S.upperSecondary).work + 2 at heq
  omega

/-- One-step span upper bound in a form suitable for strong induction. -/
theorem pMerge_span_step_le [LinearOrder α] (xs ys : List α)
    (hzero : xs.length + ys.length ≠ 0) :
    let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
    (pMerge xs ys).span ≤
      max (pMerge S.lowerPrimary S.lowerSecondary).span
          (pMerge S.upperPrimary S.upperSecondary).span +
        Nat.log 2 S.totalSize + 3 := by
  dsimp only
  let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
  have heq := pMerge_span_step_eq xs ys hzero
  have hsearch := split_search_span_le_total_log S
  change (pMerge xs ys).span ≤
    max (pMerge S.lowerPrimary S.lowerSecondary).span
        (pMerge S.upperPrimary S.upperSecondary).span +
      Nat.log 2 S.totalSize + 3
  change (pMerge xs ys).span = S.search.span +
    max (pMerge S.lowerPrimary S.lowerSecondary).span
      (pMerge S.upperPrimary S.upperSecondary).span + 2 at heq
  omega

end Chapter27
end CLRS
