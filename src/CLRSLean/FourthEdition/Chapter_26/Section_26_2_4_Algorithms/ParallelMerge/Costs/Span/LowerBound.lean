import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Span.WitnessLists
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Step

/-!
# CLRS Chapter 26.3 — Interleaved Span Lower Witness

The half-open binary search satisfies a robust reader lemma saying that its
span is at least the binary logarithm of one plus the interval length.  On the
interleaved power-of-two family, the lower recursive child is the same family
at half the size, yielding a quadratic span recurrence.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMerge
namespace Costs
namespace Span

private theorem log_two_mul_add_one_le (x : ℕ) :
    Nat.log 2 (2 * x + 1) ≤ Nat.log 2 x + 1 := by
  have hxlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) x
  have hpowpos : 0 < 2 ^ (Nat.log 2 x + 1) := pow_pos (by omega) _
  have hlt : 2 * x + 1 < 2 ^ (Nat.log 2 x + 2) := by
    rw [show Nat.log 2 x + 2 = (Nat.log 2 x + 1) + 1 by omega, pow_succ]
    omega
  have hlog := Nat.log_lt_of_lt_pow' (by omega : Nat.log 2 x + 2 ≠ 0) hlt
  omega

private theorem log_parent_le_succ_log_child (parent child : ℕ)
    (hsize : parent + 1 ≤ 2 * (child + 1) + 1) :
    Nat.log 2 (parent + 1) ≤ Nat.log 2 (child + 1) + 1 := by
  calc
    Nat.log 2 (parent + 1) ≤ Nat.log 2 (2 * (child + 1) + 1) :=
      Nat.log_monotone hsize
    _ ≤ Nat.log 2 (child + 1) + 1 :=
      log_two_mul_add_one_le (child + 1)

private theorem loop_log_succ_le_span [LinearOrder α]
    (xs : List α) (pivot : α) (lo hi : ℕ)
    (hlohi : lo ≤ hi) (hhilen : hi ≤ xs.length) :
    Nat.log 2 (hi - lo + 1) ≤
      (ParallelMerge.Internal.loop xs pivot lo hi).span := by
  induction lo, hi using ParallelMerge.Internal.loop.induct xs with
  | case1 lo hi hlt mid hnone =>
      have hmid_lt : mid < xs.length := by dsimp [mid]; omega
      rw [List.getElem?_eq_getElem hmid_lt] at hnone
      contradiction
  | case2 lo hi hlt mid x hget ihRight ihLeft =>
      have hlo_mid : lo ≤ mid := by dsimp [mid]; omega
      have hmid_hi : mid < hi := by dsimp [mid]; omega
      have ihR := ihRight (by omega) hhilen
      have ihL := ihLeft hlo_mid (le_trans (Nat.le_of_lt hmid_hi) hhilen)
      dsimp only [mid] at ihR ihL
      by_cases hxlt : x < pivot
      · rw [ParallelMerge.Internal.loop]
        simp only [hlt, if_true, mid, hget, Costed.seq_span,
          Costed.charge_span, hxlt]
        have hlevel := log_parent_le_succ_log_child
          (hi - lo) (hi - (mid + 1)) (by dsimp [mid]; omega)
        dsimp only [mid] at hlevel
        omega
      · rw [ParallelMerge.Internal.loop]
        simp only [hlt, if_true, mid, hget, Costed.seq_span,
          Costed.charge_span, hxlt, if_false]
        have hlevel := log_parent_le_succ_log_child
          (hi - lo) (mid - lo) (by dsimp [mid]; omega)
        dsimp only [mid] at hlevel
        omega
  | case3 lo hi hnlt =>
      have heq : hi = lo := by omega
      rw [ParallelMerge.Internal.loop]
      simp [heq]

private theorem binaryLowerBound_log_succ_le_span [LinearOrder α]
    (xs : List α) (pivot : α) :
    Nat.log 2 (xs.length + 1) ≤ (binaryLowerBound xs pivot).span := by
  simpa [binaryLowerBound] using
    loop_log_succ_le_span xs pivot 0 xs.length (Nat.zero_le _) le_rfl

private theorem binaryLowerBound_oddKeys_span (k : ℕ) :
    k + 1 ≤
      (binaryLowerBound (oddKeys (2 ^ (k + 1))) (2 ^ (k + 1))).span := by
  have hgeneric := binaryLowerBound_log_succ_le_span
    (oddKeys (2 ^ (k + 1))) (2 ^ (k + 1))
  have hpow : Nat.log 2 (2 ^ (k + 1)) = k + 1 :=
    Nat.log_pow (by norm_num) (k + 1)
  have hmono : Nat.log 2 (2 ^ (k + 1)) ≤
      Nat.log 2 ((oddKeys (2 ^ (k + 1))).length + 1) :=
    Nat.log_monotone (by simp)
  omega

private theorem witness_lower_split (k : ℕ) :
    let n := 2 ^ (k + 1)
    let S := mergeSplit (evenKeys n) (oddKeys n) (by
      simp only [evenKeys_length, oddKeys_length]
      positivity)
    S.lowerPrimary = evenKeys (2 ^ k) ∧
      S.lowerSecondary = oddKeys (2 ^ k) ∧
      S.search = binaryLowerBound (oddKeys n) n := by
  dsimp only
  have hv := binaryLowerBound_oddKeys_value (2 ^ k) (2 ^ (k + 1)) (by
    rw [pow_succ]
    omega)
  have hv' :
      (binaryLowerBound (oddKeys (2 * 2 ^ k)) (2 * 2 ^ k)).value = 2 ^ k := by
    simpa [pow_succ, Nat.mul_comm] using hv
  have hp : 0 < 2 ^ k := pow_pos (by omega) _
  have hle : 2 ^ k ≤ 2 * 2 ^ k := by omega
  simp [mergeSplit, MergeSplit.lowerPrimary, MergeSplit.lowerSecondary,
    MergeSplit.pivotIndex, MergeSplit.splitIndex, hv', hle,
    pow_succ, Nat.mul_comm]

private theorem witness_span_step (k : ℕ) :
    2 * (pMerge (evenKeys (2 ^ (k + 1))) (oddKeys (2 ^ (k + 1)))).span ≥
      2 * (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span + (k + 1) + 4 := by
  let n := 2 ^ (k + 1)
  have hzero : (evenKeys n).length + (oddKeys n).length ≠ 0 := by simp [n]
  let S := mergeSplit (evenKeys n) (oddKeys n) (Nat.pos_of_ne_zero hzero)
  obtain ⟨hlowerP, hlowerS, hsearch⟩ := witness_lower_split k
  have hstep := pMerge_span_step_eq (evenKeys n) (oddKeys n) hzero
  change (pMerge (evenKeys n) (oddKeys n)).span =
    S.search.span +
      max (pMerge S.lowerPrimary S.lowerSecondary).span
        (pMerge S.upperPrimary S.upperSecondary).span + 2 at hstep
  have hsearchSpan : k + 1 ≤ S.search.span := by
    rw [hsearch]
    simpa [n] using binaryLowerBound_oddKeys_span k
  have hchild : (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span ≤
      max (pMerge S.lowerPrimary S.lowerSecondary).span
        (pMerge S.upperPrimary S.upperSecondary).span := by
    rw [hlowerP, hlowerS]
    exact Nat.le_max_left _ _
  have hraw : S.search.span +
        (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span + 2 ≤
      (pMerge (evenKeys n) (oddKeys n)).span := by
    rw [hstep]
    omega
  have hcost : 2 * (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span +
        (k + 1) + 4 ≤
      2 * (S.search.span +
        (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span + 2) := by
    omega
  exact hcost.trans (Nat.mul_le_mul_left 2 hraw)

private theorem witness_span_quadratic (k : ℕ) :
    (k + 1) ^ 2 ≤
      8 * (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span := by
  induction k with
  | zero =>
      have hzero : (evenKeys 1).length + (oddKeys 1).length ≠ 0 := by simp
      have hstep := pMerge_span_step_eq (evenKeys 1) (oddKeys 1) hzero
      have hbase : 2 ≤ (pMerge (evenKeys 1) (oddKeys 1)).span := by
        rw [hstep]
        omega
      norm_num only [zero_add, pow_zero]
      calc
        1 ≤ 8 * 2 := by norm_num
        _ ≤ 8 * (pMerge (evenKeys 1) (oddKeys 1)).span :=
          Nat.mul_le_mul_left 8 hbase
  | succ k ih =>
      have hstep := witness_span_step k
      nlinarith

end Span
end Costs
end ParallelMerge

/-! ## Public theorem -/

/-- Interleaved even/odd inputs attain quadratic logarithmic span on exact
powers of two, up to the explicit constant factor eight. -/
theorem pMerge_interleaved_span_lower (k : ℕ) :
    (k + 1) ^ 2 ≤
      8 * (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span := by
  exact ParallelMerge.Costs.Span.witness_span_quadratic k

end Chapter27
end CLRS
