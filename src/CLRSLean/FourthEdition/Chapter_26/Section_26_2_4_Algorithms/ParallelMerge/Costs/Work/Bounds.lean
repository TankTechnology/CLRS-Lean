import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Step
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Work.LogPotential

/-!
# CLRS Chapter 26.3 — P-MERGE Linear Work

The lower bound counts the pivot removed at every nonempty recursive node.
The upper bound uses a logarithmic potential to amortize the binary searches
over the actual midpoint/lower-bound recursion tree.

Main results:

* {lit}`pMerge_work_lower`: P-MERGE has at least linear pointwise work.
* {lit}`pMerge_work_upper`: P-MERGE has at most linear pointwise work.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMerge
namespace Costs
namespace Work

private theorem lower_of_total [LinearOrder α] (n : ℕ) :
    ∀ (xs ys : List α), xs.length + ys.length = n →
      n ≤ (pMerge xs ys).work + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs ys htotal
      by_cases hzero : xs.length + ys.length = 0
      · omega
      · let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
        have hleft_lt : S.leftSize < n := by
          calc
            S.leftSize < S.totalSize := S.leftSize_lt
            _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hright_lt : S.rightSize < n := by
          calc
            S.rightSize < S.totalSize := S.rightSize_lt
            _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hleft : S.leftSize ≤
            (pMerge S.lowerPrimary S.lowerSecondary).work + 1 :=
          ih S.leftSize hleft_lt S.lowerPrimary S.lowerSecondary rfl
        have hright : S.rightSize ≤
            (pMerge S.upperPrimary S.upperSecondary).work + 1 :=
          ih S.rightSize hright_lt S.upperPrimary S.upperSecondary rfl
        have hchildren := pMerge_childSizes_add_one S
        have hwork : (pMerge xs ys).work =
            S.search.work +
              (pMerge S.lowerPrimary S.lowerSecondary).work +
              (pMerge S.upperPrimary S.upperSecondary).work + 2 := by
          simpa only [S] using pMerge_work_step_eq xs ys hzero
        have hSn : S.totalSize = n := by
          calc
            S.totalSize = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        subst n
        omega

/-- Stronger internal-namespace upper invariant.  The subtracted logarithmic
potential prevents the binary-search charges from adding an extra logarithmic
factor.  It is visible so later divide-and-conquer algorithms can absorb their
fork charge; the top-level P-MERGE interface remains the linear bound below. -/
theorem potential_of_total [LinearOrder α] (n : ℕ) :
    ∀ (xs ys : List α), xs.length + ys.length = n →
      (pMerge xs ys).work + 8 * Nat.log 2 (n + 1) ≤ 64 * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs ys htotal
      by_cases hzero : xs.length + ys.length = 0
      · have hn : n = 0 := by omega
        subst n
        have hxs : xs = [] := by simpa using (show xs.length = 0 by omega)
        have hys : ys = [] := by simpa using (show ys.length = 0 by omega)
        subst xs
        subst ys
        simp [pMerge]
      · let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
        have hleft_lt : S.leftSize < n := by
          calc
            S.leftSize < S.totalSize := S.leftSize_lt
            _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hright_lt : S.rightSize < n := by
          calc
            S.rightSize < S.totalSize := S.rightSize_lt
            _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hleft :=
          ih S.leftSize hleft_lt S.lowerPrimary S.lowerSecondary rfl
        have hright :=
          ih S.rightSize hright_lt S.upperPrimary S.upperSecondary rfl
        change (pMerge S.lowerPrimary S.lowerSecondary).work +
          8 * Nat.log 2 (S.leftSize + 1) ≤ 64 * S.leftSize at hleft
        change (pMerge S.upperPrimary S.upperSecondary).work +
          8 * Nat.log 2 (S.rightSize + 1) ≤ 64 * S.rightSize at hright
        have hchildren := pMerge_childSizes_add_one S
        have hquarters := pMerge_childSize_le_threeQuarters S
        have hpotential := logPotential_step S.leftSize S.rightSize S.totalSize
          S.total_positive hchildren hquarters.1 hquarters.2
        have hwork : (pMerge xs ys).work ≤
            (pMerge S.lowerPrimary S.lowerSecondary).work +
              (pMerge S.upperPrimary S.upperSecondary).work +
              Nat.log 2 S.totalSize + 3 := by
          simpa only [S] using pMerge_work_step_le xs ys hzero
        have hSn : S.totalSize = n := by
          calc
            S.totalSize = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        rw [← hSn]
        omega

end Work
end Costs
end ParallelMerge

/-! ## Public theorems -/

/-- Every input element except possibly the final zero-work boundary accounts
for a pivot-placement node in the P-MERGE recursion tree. -/
theorem pMerge_work_lower [LinearOrder α] (xs ys : List α) :
    xs.length + ys.length ≤ (pMerge xs ys).work + 1 := by
  exact ParallelMerge.Costs.Work.lower_of_total
    (xs.length + ys.length) xs ys rfl

/-- The work of the actual midpoint/binary-search P-MERGE execution is linear
in the total input size. -/
theorem pMerge_work_upper [LinearOrder α] (xs ys : List α) :
    (pMerge xs ys).work ≤ 64 * (xs.length + ys.length + 1) := by
  have h := ParallelMerge.Costs.Work.potential_of_total
    (xs.length + ys.length) xs ys rfl
  omega

end Chapter27
end CLRS
