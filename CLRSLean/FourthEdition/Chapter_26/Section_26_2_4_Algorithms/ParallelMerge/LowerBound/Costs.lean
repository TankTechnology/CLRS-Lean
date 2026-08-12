import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.LowerBound.Definitions

/-!
# CLRS Chapter 26.3 — Binary Lower-Bound Costs

The lower-bound helper is sequential: every comparison contributes one unit to
both work and span.  Its live interval is at least halved by every comparison,
which gives the logarithmic public bound.

Main results:

* {lit}`binaryLowerBound_work_le_log` bounds work on every input.
* {lit}`binaryLowerBound_span_eq_work` records sequentiality.
* {lit}`binaryLowerBound_span_le_log` transfers the work bound to span.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMerge
namespace LowerBound

private theorem log_half_add_one_le (n : ℕ) (hn : 2 ≤ n) :
    Nat.log 2 (n / 2) + 1 ≤ Nat.log 2 n := by
  rw [Nat.log_div_base]
  have hlogpos : 1 ≤ Nat.log 2 n := Nat.log_pos (by omega) hn
  omega

private theorem comparison_cost_le_log (n child work : ℕ)
    (hn : 0 < n)
    (hchild : child ≤ n / 2)
    (hwork : work ≤ Nat.log 2 child + 1)
    (hzero : child = 0 → work = 0) :
    1 + work ≤ Nat.log 2 n + 1 := by
  by_cases hc : child = 0
  · simp [hzero hc]
  · have hcpos : 0 < child := Nat.pos_of_ne_zero hc
    have hn_two : 2 ≤ n := by omega
    have hlogmono : Nat.log 2 child ≤ Nat.log 2 (n / 2) :=
      Nat.log_monotone hchild
    have hhalf := log_half_add_one_le n hn_two
    omega

/-- On every valid half-open interval, binary-search work is logarithmic in
the interval length.  The proof is strong recursion through the generated loop
induction principle; both recursive intervals are bounded by half the parent. -/
private theorem loop_work_le_log [LinearOrder α]
    (xs : List α) (pivot : α) (lo hi : ℕ)
    (hlohi : lo ≤ hi) (hhilen : hi ≤ xs.length) :
    (Internal.loop xs pivot lo hi).work ≤ Nat.log 2 (hi - lo) + 1 := by
  induction lo, hi using Internal.loop.induct xs with
  | case1 lo hi hlt mid hnone =>
      have hmid_lt : mid < xs.length := by dsimp [mid]; omega
      rw [List.getElem?_eq_getElem hmid_lt] at hnone
      contradiction
  | case2 lo hi hlt mid x hget ihRight ihLeft =>
      have hlo_mid : lo ≤ mid := by dsimp [mid]; omega
      have hmid_hi : mid < hi := by dsimp [mid]; omega
      have hright_bound : hi - (mid + 1) ≤ (hi - lo) / 2 := by
        dsimp [mid]
        omega
      have hleft_bound : mid - lo ≤ (hi - lo) / 2 := by
        dsimp [mid]
        omega
      have ihR := ihRight (by omega) hhilen
      have ihL := ihLeft hlo_mid (le_trans (Nat.le_of_lt hmid_hi) hhilen)
      by_cases hxlt : x < pivot
      · rw [Internal.loop]
        simp only [hlt, if_true, mid, hget, Costed.seq_work, Costed.charge_work, hxlt]
        apply comparison_cost_le_log (hi - lo) (hi - (mid + 1))
          (Internal.loop xs pivot (mid + 1) hi).work (by omega) hright_bound ihR
        intro hz
        have heq : mid + 1 = hi := by omega
        simp [heq, Internal.loop]
      · rw [Internal.loop]
        simp only [hlt, if_true, mid, hget, Costed.seq_work, Costed.charge_work,
          hxlt, if_false]
        apply comparison_cost_le_log (hi - lo) (mid - lo)
          (Internal.loop xs pivot lo mid).work (by omega) hleft_bound ihL
        intro hz
        have heq : mid = lo := by omega
        simp [heq, Internal.loop]
  | case3 lo hi hnlt =>
      rw [Internal.loop]
      simp only [hnlt, if_false, Costed.pure_work]
      omega

/-- The internal lower-bound computation has identical work and span because it
performs no parallel composition. -/
private theorem loop_span_eq_work [LinearOrder α]
    (xs : List α) (pivot : α) (lo hi : ℕ) :
    (Internal.loop xs pivot lo hi).span = (Internal.loop xs pivot lo hi).work := by
  induction lo, hi using Internal.loop.induct xs with
  | case1 lo hi hlt mid hnone =>
      rw [Internal.loop]
      simp [hlt, mid, hnone]
  | case2 lo hi hlt mid x hget ihRight ihLeft =>
      by_cases hxlt : x < pivot
      · rw [Internal.loop]
        simp [hlt, mid, hget, hxlt, ihRight]
      · rw [Internal.loop]
        simp [hlt, mid, hget, hxlt, ihLeft]
  | case3 lo hi hnlt =>
      rw [Internal.loop]
      simp [hnlt]

end LowerBound
end ParallelMerge

/-! ## Public theorems -/

/-- Binary lower bound uses at most `log₂(length) + 1` comparisons. -/
theorem binaryLowerBound_work_le_log [LinearOrder α]
    (xs : List α) (pivot : α) :
    (binaryLowerBound xs pivot).work ≤ Nat.log 2 xs.length + 1 := by
  simpa [binaryLowerBound] using
    ParallelMerge.LowerBound.loop_work_le_log xs pivot 0 xs.length
      (Nat.zero_le _) le_rfl

/-- Binary lower bound is sequential, so its span equals its work exactly. -/
theorem binaryLowerBound_span_eq_work [LinearOrder α]
    (xs : List α) (pivot : α) :
    (binaryLowerBound xs pivot).span = (binaryLowerBound xs pivot).work := by
  exact ParallelMerge.LowerBound.loop_span_eq_work xs pivot 0 xs.length

/-- The sequential span of binary lower bound is logarithmic as well. -/
theorem binaryLowerBound_span_le_log [LinearOrder α]
    (xs : List α) (pivot : α) :
    (binaryLowerBound xs pivot).span ≤ Nat.log 2 xs.length + 1 := by
  rw [binaryLowerBound_span_eq_work]
  exact binaryLowerBound_work_le_log xs pivot

end Chapter27
end CLRS
