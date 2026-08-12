import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Span.Envelope

/-!
# CLRS Chapter 26.3 — Pointwise P-MERGE Span Upper Bound

This module connects the executable split to the monotone three-quarter
envelope and publishes the quadratic-logarithmic upper bound.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMerge
namespace Costs
namespace Span

private theorem log_charge_le_removed (n : ℕ) (hn : 9 ≤ n) :
    Nat.log 2 n + 3 ≤ 8 * (n - shrink n) := by
  have hlog := Nat.log_le_self 2 n
  simp only [shrink]
  omega

private theorem linear_of_total [LinearOrder α] (n : ℕ) :
    ∀ (xs ys : List α), xs.length + ys.length = n →
      (pMerge xs ys).span ≤ 8 * n := by
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
        have hnpos : 0 < n := by omega
        have hSn : S.totalSize = n := by
          calc
            S.totalSize = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hleft_lt : S.leftSize < n := by
          rw [← hSn]
          exact S.leftSize_lt
        have hright_lt : S.rightSize < n := by
          rw [← hSn]
          exact S.rightSize_lt
        have hleft := ih S.leftSize hleft_lt
          S.lowerPrimary S.lowerSecondary rfl
        have hright := ih S.rightSize hright_lt
          S.upperPrimary S.upperSecondary rfl
        have hquarters := pMerge_childSize_le_threeQuarters S
        have hstep : (pMerge xs ys).span ≤
            max (pMerge S.lowerPrimary S.lowerSecondary).span
                (pMerge S.upperPrimary S.upperSecondary).span +
              Nat.log 2 n + 3 := by
          have := pMerge_span_step_le xs ys hzero
          simpa only [S, hSn] using this
        have hmax : max (pMerge S.lowerPrimary S.lowerSecondary).span
              (pMerge S.upperPrimary S.upperSecondary).span ≤
            8 * shrink n := by
          apply max_le
          · calc
              (pMerge S.lowerPrimary S.lowerSecondary).span ≤
                  8 * S.leftSize := hleft
              _ ≤ 8 * shrink n := Nat.mul_le_mul_left 8 (by simpa [hSn, shrink]
                using hquarters.1)
          · calc
              (pMerge S.upperPrimary S.upperSecondary).span ≤
                  8 * S.rightSize := hright
              _ ≤ 8 * shrink n := Nat.mul_le_mul_left 8 (by simpa [hSn, shrink]
                using hquarters.2)
        by_cases hnsmall : n < 9
        · have hmaxSmall : max (pMerge S.lowerPrimary S.lowerSecondary).span
              (pMerge S.upperPrimary S.upperSecondary).span ≤ 8 * (n - 1) := by
            apply max_le
            · exact hleft.trans (Nat.mul_le_mul_left 8 (by omega))
            · exact hright.trans (Nat.mul_le_mul_left 8 (by omega))
          calc
            (pMerge xs ys).span ≤
                max (pMerge S.lowerPrimary S.lowerSecondary).span
                    (pMerge S.upperPrimary S.upperSecondary).span +
                  Nat.log 2 n + 3 := hstep
            _ ≤ 8 * (n - 1) + Nat.log 2 n + 3 := by omega
            _ ≤ 8 * n := by interval_cases n <;> norm_num
        · have hcharge := log_charge_le_removed n (by omega)
          omega

private theorem small_linear_le_quadratic (n : ℕ) (hn : n < 64) :
    8 * n ≤ 64 * (Nat.log 2 n + 1) ^ 2 := by
  interval_cases n <;> norm_num

private theorem envelope_of_total [LinearOrder α] (n : ℕ) :
    ∀ (xs ys : List α), xs.length + ys.length = n →
      (pMerge xs ys).span ≤ pMergeSpanUpper n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs ys htotal
      by_cases hnsmall : n < 64
      · calc
          (pMerge xs ys).span ≤ 8 * n := linear_of_total n xs ys htotal
          _ ≤ 64 * (Nat.log 2 n + 1) ^ 2 := small_linear_le_quadratic n hnsmall
          _ = pMergeSpanUpper n := (pMergeSpanUpper_small n hnsmall).symm
      · have hn64 : 64 ≤ n := by omega
        have hzero : xs.length + ys.length ≠ 0 := by omega
        let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
        have hSn : S.totalSize = n := by
          calc
            S.totalSize = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hleft_lt : S.leftSize < n := by rw [← hSn]; exact S.leftSize_lt
        have hright_lt : S.rightSize < n := by rw [← hSn]; exact S.rightSize_lt
        have hleft := ih S.leftSize hleft_lt
          S.lowerPrimary S.lowerSecondary rfl
        have hright := ih S.rightSize hright_lt
          S.upperPrimary S.upperSecondary rfl
        have hquarters := pMerge_childSize_le_threeQuarters S
        have hleftE : (pMerge S.lowerPrimary S.lowerSecondary).span ≤
            pMergeSpanUpper (shrink n) := hleft.trans
          (pMergeSpanUpper_monotone (by simpa [hSn, shrink] using hquarters.1))
        have hrightE : (pMerge S.upperPrimary S.upperSecondary).span ≤
            pMergeSpanUpper (shrink n) := hright.trans
          (pMergeSpanUpper_monotone (by simpa [hSn, shrink] using hquarters.2))
        have hstep := pMerge_span_step_le xs ys hzero
        rw [pMergeSpanUpper_large n hn64]
        change (pMerge xs ys).span ≤
          pMergeSpanUpper (shrink n) + Nat.log 2 n + 3
        change (pMerge xs ys).span ≤
          max (pMerge S.lowerPrimary S.lowerSecondary).span
              (pMerge S.upperPrimary S.upperSecondary).span +
            Nat.log 2 S.totalSize + 3 at hstep
        rw [hSn] at hstep
        omega

end Span
end Costs
end ParallelMerge

/-! ## Public theorem -/

/-- P-MERGE has pointwise `O(log² n)` span on every pair of inputs. -/
theorem pMerge_span_upper [LinearOrder α] (xs ys : List α) :
    (pMerge xs ys).span ≤
      64 * (Nat.log 2 (xs.length + ys.length) + 1) ^ 2 := by
  exact (ParallelMerge.Costs.Span.envelope_of_total
    (xs.length + ys.length) xs ys rfl).trans
      (ParallelMerge.Costs.Span.pMergeSpanUpper_le_quadratic _)

end Chapter27
end CLRS
