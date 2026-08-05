import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Step
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.MapInvariance
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.WitnessInput
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span.LowerBound

/-!
# CLRS Chapter 27.3 — P-MERGE-SORT Cubic-Log Span Witness

Each witness level recursively sorts an order-embedded copy of the preceding
level, then merges the canonical interleaved even/odd lists.  Order-embedding
cost invariance preserves the recursive critical path, while the P-MERGE
witness contributes a quadratic term at every level.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMergeSort
namespace Costs
namespace Span

private theorem double_strictMono : StrictMono (fun x : ℕ => 2 * x) := by
  intro a b hab
  change 2 * a < 2 * b
  omega

/-- One witness level contains the preceding witness critical path plus the
quadratic interleaved P-MERGE critical path. -/
private theorem witness_span_step (k : ℕ) :
    (pMergeSort (worstMergeSortInput k)).span +
        (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span + 1 ≤
      (pMergeSort (worstMergeSortInput (k + 1))).span := by
  have hsmall : ¬ (worstMergeSortInput (k + 1)).length ≤ 1 := by
    rw [worstMergeSortInput_length, pow_succ]
    have hp : 0 < 2 ^ k := pow_pos (by omega) _
    omega
  have hmid : (worstMergeSortInput (k + 1)).length / 2 = 2 ^ k := by
    rw [worstMergeSortInput_length, pow_succ]
    omega
  have hstep := pMergeSort_span_step_eq
    (worstMergeSortInput (k + 1)) hsmall
  change (pMergeSort (worstMergeSortInput (k + 1))).span =
    max
      (pMergeSort ((worstMergeSortInput (k + 1)).take
        ((worstMergeSortInput (k + 1)).length / 2))).span
      (pMergeSort ((worstMergeSortInput (k + 1)).drop
        ((worstMergeSortInput (k + 1)).length / 2))).span + 1 +
    (pMerge
      (pMergeSort ((worstMergeSortInput (k + 1)).take
        ((worstMergeSortInput (k + 1)).length / 2))).value
      (pMergeSort ((worstMergeSortInput (k + 1)).drop
        ((worstMergeSortInput (k + 1)).length / 2))).value).span at hstep
  rw [hmid, witness_take_half, witness_drop_half,
    sorted_even_half, sorted_odd_half] at hstep
  have hmapCost := pMergeSort_map (fun x : ℕ => 2 * x) double_strictMono
    (worstMergeSortInput k).length (worstMergeSortInput k) rfl
  have hmapSpan := congrArg Costed.span hmapCost
  simp only [Costed.map_span] at hmapSpan
  rw [hmapSpan] at hstep
  omega

/-- Inductive cubic accumulation for the complete witness family. -/
private theorem witness_span_cubic (k : ℕ) :
    (k + 1) ^ 3 ≤ 64 * (pMergeSort (worstMergeSortInput k)).span := by
  induction k with
  | zero =>
      norm_num only [zero_add, one_pow]
      rw [pMergeSort]
      simp only [worstMergeSortInput, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.reduceLeDiff]
      norm_num
  | succ k ih =>
      have hstep := witness_span_step k
      have hmerge := pMerge_interleaved_span_lower k
      nlinarith [sq_nonneg (k : ℤ)]

end Span
end Costs
end ParallelMergeSort

/-! ## Public theorem -/

/-- The recursively interleaved power-of-two family has cubic-logarithmic
P-MERGE-SORT span from below. -/
theorem pMergeSort_worstFamily_span_lower (k : ℕ) :
    (k + 1) ^ 3 ≤ 64 * (pMergeSort (worstMergeSortInput k)).span := by
  exact ParallelMergeSort.Costs.Span.witness_span_cubic k

end Chapter27
end CLRS
