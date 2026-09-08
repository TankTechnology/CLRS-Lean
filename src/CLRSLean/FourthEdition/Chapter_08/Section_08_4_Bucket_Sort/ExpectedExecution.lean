import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Expected work of the indexed bucket execution

The random assignment gives independent uniform bucket indices. Final ranks
may depend arbitrarily on the assignment: the insertion work bound holds for
every order within each bucket. The expected-work theorem is separate from
output sortedness, which additionally requires the cross-bucket rank condition.
-/

namespace CLRS.Chapter08

/-- The actual run is bounded by a linear term and twice the occupancy budget. -/
theorem bucketExecutionWork_le_budget (a : Fin n → Fin n) (rank : Fin n → Nat) :
    ((bucketSortByRankWithCost n (fun i => (a i : Nat)) rank (List.finRange n)).2 : ℝ) ≤
      6 * (n : ℝ) + 2 * textbookBucketSortCost n a := by
  have h := bucketSortByRankWithCost_work_le n (fun i : Fin n => (a i : Nat)) rank
    (List.finRange n) (fun i _ => (a i).isLt)
  rw [List.length_finRange] at h
  have hc : ((bucketSortByRankWithCost n (fun i => (a i : Nat)) rank
      (List.finRange n)).2 : ℝ) ≤ 2 * (n : ℝ) + 4 * n +
      2 * (bucketSortByRankCost n (fun i => (a i : Nat)) (List.finRange n) : ℝ) := by
    exact_mod_cast h
  rw [bucketSortByRankCost_eq_textbookBucketSortCost] at hc
  linarith

/-- At most twelve work units per input element in expectation under uniform buckets. -/
theorem expectedBucketExecutionWork_le (n : Nat) (hn : 0 < n)
    (rank : (Fin n → Fin n) → Fin n → Nat) :
    CLRS.Probability.fintypeExpect (fun a : Fin n → Fin n =>
      ((bucketSortByRankWithCost n (fun i => (a i : Nat)) (rank a)
        (List.finRange n)).2 : ℝ)) ≤ 12 * (n : ℝ) := by
  classical
  letI : Nonempty (Fin n → Fin n) := ⟨id⟩
  have hm : CLRS.Probability.fintypeExpect (fun a : Fin n → Fin n =>
      ((bucketSortByRankWithCost n (fun i => (a i : Nat)) (rank a)
        (List.finRange n)).2 : ℝ)) ≤
      CLRS.Probability.fintypeExpect (fun a : Fin n → Fin n =>
        6 * (n : ℝ) + 2 * textbookBucketSortCost n a) := by
    unfold CLRS.Probability.fintypeExpect
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum (fun a _ => bucketExecutionWork_le_budget a (rank a))
  have hlin : CLRS.Probability.fintypeExpect (fun a : Fin n → Fin n =>
      6 * (n : ℝ) + 2 * textbookBucketSortCost n a) =
      6 * (n : ℝ) + 2 * expectedBucketSortCost n := by
    rw [CLRS.Probability.fintypeExpect_add]
    rw [CLRS.Probability.fintypeExpect_const (by exact Fintype.card_ne_zero)]
    have hmul : CLRS.Probability.fintypeExpect (fun a : Fin n → Fin n =>
        2 * textbookBucketSortCost n a) =
        2 * CLRS.Probability.fintypeExpect (textbookBucketSortCost n) := by
      simp only [CLRS.Probability.fintypeExpect, ← Finset.mul_sum, mul_div_assoc]
    rw [hmul, fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost n hn]
  rw [hlin] at hm
  have hbudget := expectedBucketSortCost_linear_bound n hn
  linarith

/-- Uniform bucket assignments give linear expected work for the actual execution. -/
theorem expectedBucketExecutionWork_isBigO
    (rank : ∀ n, (Fin n → Fin n) → Fin n → Nat) :
    Chapter03.isBigO (fun n : Nat =>
      CLRS.Probability.fintypeExpect (fun a : Fin n → Fin n =>
        ((bucketSortByRankWithCost n (fun i => (a i : Nat)) (rank n a)
          (List.finRange n)).2 : ℝ))) (fun n : Nat => (n : ℝ)) := by
  rw [Chapter03.isBigO_iff]
  refine ⟨12, by norm_num, 1, ?_⟩
  intro n hn
  rw [abs_of_nonneg (CLRS.Probability.fintypeExpect_nonneg (by intro a; positivity)),
    abs_of_nonneg (Nat.cast_nonneg n)]
  exact expectedBucketExecutionWork_le n (by omega) (rank n)

end CLRS.Chapter08
