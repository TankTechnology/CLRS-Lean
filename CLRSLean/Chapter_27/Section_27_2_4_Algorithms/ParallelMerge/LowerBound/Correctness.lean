import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound.Definitions

/-!
# CLRS Chapter 27.3 — Binary Lower-Bound Correctness

This module proves the partition specification used by P-MERGE's sequential
binary search.  The internal proof follows the half-open search interval and
makes both boundary invariants explicit.

Main results:

* {lit}`binaryLowerBound_partition` proves the complete lower-bound partition.
* {lit}`binaryLowerBound_index_le_length` proves the index bound even for an
  unsorted input list.
-/

namespace CLRS
namespace Chapter27

/-- The insertion index splits a list into values strictly below the pivot and
values greater than or equal to the pivot. -/
structure LowerBoundSpec [LinearOrder α] (xs : List α) (pivot : α) (i : ℕ) : Prop where
  index_le_length : i ≤ xs.length
  left_lt : ∀ x ∈ xs.take i, x < pivot
  right_ge : ∀ x ∈ xs.drop i, pivot ≤ x

namespace ParallelMerge
namespace LowerBound

/-- The strong invariant of the half-open interval {lit}`[lo, hi)`: all indices
strictly before {lit}`lo` are already known to be below the pivot, while all
indices at or after {lit}`hi` are already known to be at least the pivot. -/
private structure LoopInvariant [LinearOrder α] (xs : List α) (pivot : α)
    (lo hi : ℕ) : Prop where
  lo_le_hi : lo ≤ hi
  hi_le_length : hi ≤ xs.length
  left_lt : ∀ j : Fin xs.length, j.1 < lo → xs.get j < pivot
  right_ge : ∀ j : Fin xs.length, hi ≤ j.1 → pivot ≤ xs.get j

private theorem loopInvariant_to_spec [LinearOrder α]
    {xs : List α} {pivot : α} {i : ℕ}
    (hinv : LoopInvariant xs pivot i i) : LowerBoundSpec xs pivot i := by
  constructor
  · exact hinv.hi_le_length
  · intro x hx
    obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp hx
    have hj_lt_i : j < i := by
      rw [List.length_take] at hj
      omega
    have hj_lt_len : j < xs.length := by
      rw [List.length_take] at hj
      omega
    have hlt := hinv.left_lt ⟨j, hj_lt_len⟩ hj_lt_i
    rw [List.get_eq_getElem, ← List.getElem_take (h := hj)] at hlt
    simpa [hval] using hlt
  · intro x hx
    obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp hx
    have hglobal : i + j < xs.length := by
      rw [List.length_drop] at hj
      omega
    have hge := hinv.right_ge ⟨i + j, hglobal⟩ (by simp)
    rw [List.get_eq_getElem, ← List.getElem_drop (h := hj)] at hge
    simpa [hval] using hge

/-- The lower-bound loop preserves its two boundary facts and returns the
unique global partition index once the interval closes. -/
private theorem loop_correct [LinearOrder α] (xs : List α) (pivot : α) (lo hi : ℕ)
    (hinv : LoopInvariant xs pivot lo hi)
    (hxs : xs.Pairwise (· ≤ ·)) :
    LowerBoundSpec xs pivot (Internal.loop xs pivot lo hi).value := by
  induction lo, hi using Internal.loop.induct xs with
  | case1 lo hi hlohi mid hnone =>
      have hmid_lt : (lo + hi) / 2 < xs.length := by
        have := hinv.hi_le_length
        omega
      rw [List.getElem?_eq_getElem hmid_lt] at hnone
      contradiction
  | case2 lo hi hlohi mid x hget ihRight ihLeft =>
      have hlo_mid : lo ≤ mid := by
        dsimp [mid]
        omega
      have hmid_hi : mid < hi := by
        dsimp [mid]
        omega
      have hmid_len : mid < xs.length := lt_of_lt_of_le hmid_hi hinv.hi_le_length
      have hx_at : xs.get ⟨mid, hmid_len⟩ = x := by
        obtain ⟨_, hx⟩ := List.getElem?_eq_some_iff.mp hget
        simpa [List.get_eq_getElem] using hx
      by_cases hxlt : x < pivot
      · rw [Internal.loop]
        simp only [hlohi, if_true, mid, hget, Costed.seq_value, hxlt]
        apply ihRight
        · refine ⟨by omega, hinv.hi_le_length, ?_, hinv.right_ge⟩
          intro j hj
          by_cases hjlo : j.1 < lo
          · exact hinv.left_lt j hjlo
          by_cases hjmid : j.1 = mid
          · have hj_eq : j = ⟨mid, hmid_len⟩ := Fin.ext hjmid
            rw [hj_eq, hx_at]
            exact hxlt
          · have hj_lt_mid : j.1 < mid := by omega
            have hle := hxs.rel_get_of_lt (a := j) (b := ⟨mid, hmid_len⟩) hj_lt_mid
            rw [hx_at] at hle
            exact lt_of_le_of_lt hle hxlt
      · have hpivot_le_x : pivot ≤ x := le_of_not_gt hxlt
        rw [Internal.loop]
        simp only [hlohi, if_true, mid, hget, Costed.seq_value, hxlt, if_false]
        apply ihLeft
        · refine ⟨hlo_mid, le_trans (Nat.le_of_lt hmid_hi) hinv.hi_le_length,
            hinv.left_lt, ?_⟩
          intro j hj
          by_cases hjmid : j.1 = mid
          · have hj_eq : j = ⟨mid, hmid_len⟩ := Fin.ext hjmid
            rw [hj_eq, hx_at]
            exact hpivot_le_x
          · have hmid_lt_j : mid < j.1 := by omega
            have hle := hxs.rel_get_of_lt (a := ⟨mid, hmid_len⟩) (b := j) hmid_lt_j
            rw [hx_at] at hle
            exact le_trans hpivot_le_x hle
  | case3 lo hi hnlt =>
      have hlo_eq_hi : lo = hi := Nat.le_antisymm hinv.lo_le_hi (Nat.le_of_not_gt hnlt)
      rw [Internal.loop]
      simp only [hnlt, if_false, Costed.pure_value]
      exact loopInvariant_to_spec (hlo_eq_hi ▸ hinv)

/-- Independently of sortedness, the internal search never returns beyond its
upper interval endpoint. -/
private theorem loop_value_le_hi [LinearOrder α] (xs : List α) (pivot : α) (lo hi : ℕ)
    (hlohi : lo ≤ hi) (hhilen : hi ≤ xs.length) :
    (Internal.loop xs pivot lo hi).value ≤ hi := by
  induction lo, hi using Internal.loop.induct xs with
  | case1 lo hi hlt mid hnone =>
      have hmid_lt : (lo + hi) / 2 < xs.length := by omega
      rw [List.getElem?_eq_getElem hmid_lt] at hnone
      contradiction
  | case2 lo hi hlt mid x hget ihRight ihLeft =>
      have hlo_mid : lo ≤ mid := by dsimp [mid]; omega
      have hmid_hi : mid < hi := by dsimp [mid]; omega
      by_cases hxlt : x < pivot
      · rw [Internal.loop]
        simp only [hlt, if_true, mid, hget, Costed.seq_value, hxlt]
        exact ihRight (by omega) hhilen
      · rw [Internal.loop]
        simp only [hlt, if_true, mid, hget, Costed.seq_value, hxlt, if_false]
        exact le_trans (ihLeft hlo_mid (le_trans (Nat.le_of_lt hmid_hi) hhilen))
          (Nat.le_of_lt hmid_hi)
  | case3 lo hi hnlt =>
      rw [Internal.loop]
      simp only [hnlt, if_false, Costed.pure_value]
      exact hlohi

end LowerBound
end ParallelMerge

/-! ## Public theorems -/

/-- Binary lower bound returns a valid index even when the input is unsorted. -/
theorem binaryLowerBound_index_le_length [LinearOrder α]
    (xs : List α) (pivot : α) :
    (binaryLowerBound xs pivot).value ≤ xs.length := by
  exact ParallelMerge.LowerBound.loop_value_le_hi xs pivot 0 xs.length
    (Nat.zero_le _) le_rfl

/-- On a sorted input, binary lower bound produces the textbook strict-left,
nonstrict-right partition, including the correct behavior on duplicates. -/
theorem binaryLowerBound_partition [LinearOrder α] (xs : List α) (pivot : α)
    (hxs : xs.Pairwise (· ≤ ·)) :
    LowerBoundSpec xs pivot (binaryLowerBound xs pivot).value := by
  apply ParallelMerge.LowerBound.loop_correct xs pivot 0 xs.length
  · exact ⟨Nat.zero_le _, le_rfl, by simp, by simp⟩
  · exact hxs

end Chapter27
end CLRS
