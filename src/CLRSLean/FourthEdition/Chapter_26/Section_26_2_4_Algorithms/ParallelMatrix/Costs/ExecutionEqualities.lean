import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Definitions
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.Definitions

/-!
# CLRS Section 26.2 — Matrix Execution Cost Equalities

This module connects the exact work and span carried by executable
{lit}`P-ADD` and {lit}`P-MATMUL` results to their natural-number recurrences.
The equalities hold at every matrix depth over any ring.

Main results:

- Theorem {lit}`pAdd_work_eq`: executable {lit}`P-ADD` work equals {lit}`pAddWork`.
- Theorem {lit}`pAdd_span_eq`: executable {lit}`P-ADD` span equals {lit}`pAddSpan`.
- Theorem {lit}`pMatMul_work_eq`: executable {lit}`P-MATMUL` work equals
  {lit}`pMatMulExecWork`.
- Theorem {lit}`pMatMul_span_eq`: executable {lit}`P-MATMUL` span equals
  {lit}`pMatMulExecSpan`.
-/

namespace CLRS
namespace Chapter27

universe u

/-- Halving the next power of two returns the preceding power. -/
private theorem two_pow_succ_div_two (k : ℕ) : 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ]
  omega

/-- Every non-base power of two has size at least two. -/
private theorem two_le_two_pow_succ (k : ℕ) : 2 ≤ 2 ^ (k + 1) := by
  rw [pow_succ]
  have := Nat.one_le_pow k 2 (by norm_num)
  omega

/-- Exact work carried by executable {lit}`P-ADD` at matrix depth {lit}`k`. -/
theorem pAdd_work_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pAdd R k A B).work = pAddWork (2 ^ k) := by
  induction k with
  | zero => simp [pAdd, pAddWork]
  | succ k ih =>
      rw [pAddWork_unfold (two_le_two_pow_succ k), two_pow_succ_div_two]
      simp [pAdd, ih]
      omega

/-- Exact span carried by executable {lit}`P-ADD` at matrix depth {lit}`k`. -/
theorem pAdd_span_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pAdd R k A B).span = pAddSpan (2 ^ k) := by
  induction k with
  | zero => simp [pAdd, pAddSpan]
  | succ k ih =>
      rw [pAddSpan_unfold (two_le_two_pow_succ k), two_pow_succ_div_two]
      simp [pAdd, ih]

/-- Exact work carried by executable {lit}`P-MATMUL` at matrix depth {lit}`k`. -/
theorem pMatMul_work_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pMatMul R k A B).work = pMatMulExecWork (2 ^ k) := by
  induction k with
  | zero => simp [pMatMul, pMatMulExecWork]
  | succ k ih =>
      rw [pMatMulExecWork_unfold (two_le_two_pow_succ k),
        two_pow_succ_div_two]
      simp [pMatMul, ih, pAdd_work_eq]
      omega

/-- Exact span carried by executable {lit}`P-MATMUL` at matrix depth {lit}`k`. -/
theorem pMatMul_span_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pMatMul R k A B).span = pMatMulExecSpan (2 ^ k) := by
  induction k with
  | zero => simp [pMatMul, pMatMulExecSpan]
  | succ k ih =>
      rw [pMatMulExecSpan_unfold (two_le_two_pow_succ k),
        two_pow_succ_div_two]
      simp [pMatMul, ih, pAdd_span_eq]

end Chapter27
end CLRS
