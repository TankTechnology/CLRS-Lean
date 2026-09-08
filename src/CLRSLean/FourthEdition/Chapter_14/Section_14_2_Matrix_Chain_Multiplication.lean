import CLRSLean.Chapter_15.Section_15_2_Matrix_Chain_Multiplication

open Finset
open scoped BigOperators

/-!
# Section 14.2 — Matrix-chain multiplication

The legacy {name}`CLRS.Chapter15.matrixChainOpt` and
{name}`CLRS.Chapter15.matrixChainSplit` recursively evaluate an optimization
specification; they do not store a dynamic-programming table. This section
retains their arithmetic table-size and candidate-budget formulas.

The {lit}`Execution` companion supplies {lit}`MatrixChainExecution.execute`:
actual arrays of interval-length rows storing costs and selected splits. Each
candidate reads strictly shorter stored intervals. Its correctness theorem
identifies every stored cost and proves the selected split attains it. Table
reconstruction reads those stored splits without rerunning the recurrence.
The cell and candidate counters are accumulated by that same fill execution.

The parameter {lit}`N` in the execution is the largest matrix index, so indices
{lit}`0..N` describe {lit}`N + 1` matrices. Array access, dimension lookup, and
arithmetic are primitive events; allocation/copying and arithmetic bit costs
are excluded. The formulas below alone are not execution-cost proofs; use the
companion's {lit}`execute_cells` and {lit}`execute_candidateVisits` interfaces.

Notation conventions used in this section:

- `dims` : the dimension table, {lit}`dims i` = the number of rows of matrix {lit}`Aᵢ`
- `n` : the number of matrices
-/

namespace CLRS
namespace Chapter15

/-! ## Space and time of the table algorithm -/

/-- The number of distinct {lit}`(i, j)` subproblems with {lit}`0 ≤ i ≤ j ≤ n`,
    an arithmetic interval-count formula. -/
def matrixChainSpace (n : Nat) : Nat :=
  (n + 1) * (n + 2) / 2

/-- An abstract split-count formula: for each
    interval {lit}`[i, j]` there are {lit}`j - i` candidate split points. -/
def matrixChainTime (n : Nat) : Nat :=
  (Finset.range (n + 1)).sum (fun j => (Finset.range j).sum (fun i => j - i))

/-- The table has `(n + 1)(n + 2) / 2` entries. -/
theorem matrixChainSpace_eq (n : Nat) :
    matrixChainSpace n = (n + 1) * (n + 2) / 2 := rfl

/-- Quadratic bound on the interval-count formula. -/
theorem matrixChainSpace_le_square (n : Nat) : matrixChainSpace n ≤ (n + 2) ^ 2 := by
  unfold matrixChainSpace
  calc
    (n + 1) * (n + 2) / 2 ≤ (n + 1) * (n + 2) := Nat.div_le_self _ _
    _ ≤ (n + 2) * (n + 2) := Nat.mul_le_mul_right _ (by omega : n + 1 ≤ n + 2)
    _ = (n + 2) ^ 2 := by rw [pow_two]

/-- Cubic bound on the abstract split-count formula. -/
theorem matrixChainTime_le_cubic (n : Nat) : matrixChainTime n ≤ (n + 1) ^ 3 := by
  unfold matrixChainTime
  calc
    (Finset.range (n + 1)).sum (fun j => (Finset.range j).sum (fun i => j - i))
        ≤ (Finset.range (n + 1)).sum (fun j => j ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          calc
            (Finset.range j).sum (fun i => j - i) ≤ (Finset.range j).sum (fun _ => j) := by
              apply Finset.sum_le_sum
              intro i hi
              omega
            _ = j * j := by simp [Finset.sum_const, Finset.card_range]
            _ = j ^ 2 := by rw [pow_two]
    _ ≤ (n + 1) * n ^ 2 := by
      have hbound : ∀ j ∈ Finset.range (n + 1), j ^ 2 ≤ n ^ 2 := by
        intro j hj
        have hjle : j ≤ n := by simpa [mem_range] using hj
        exact Nat.pow_le_pow_left hjle 2
      simpa [Finset.card_range, nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (Finset.range (n + 1)) (fun j => j ^ 2) (n ^ 2)
          (by intro j hj; exact hbound j hj))
    _ ≤ (n + 1) ^ 3 := by
      have h : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
      have h' : (n + 1) * n ^ 2 ≤ (n + 1) * (n + 1) ^ 2 := Nat.mul_le_mul_left (n + 1) h
      rw [show (n + 1) ^ 3 = (n + 1) * (n + 1) ^ 2 by rw [pow_succ, mul_comm]]
      exact h'

end Chapter15
end CLRS
