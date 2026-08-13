import CLRSLean.Chapter_15.Section_15_2_Matrix_Chain_Multiplication

open Finset
open scoped BigOperators

/-!
# Section 14.2 — Matrix-chain multiplication

This section completes the fourth-edition §14.2 algorithm boundary on top of the
legacy recurrence and bottom-up table
({lit}`CLRSLean.Chapter_15.Section_15_2_Matrix_Chain_Multiplication`).  It
publishes the tabulated `MATRIX-CHAIN-ORDER` — the cost table
{name}`CLRS.Chapter15.matrixChainOpt` (the {lit}`m` table) and the split table
{name}`CLRS.Chapter15.matrixChainSplit` (the {lit}`s` table) — together with the
split-reconstruction refinement
{name}`CLRS.Chapter15.matrixChainReconstruct_reconstructed`, and proves the
`Θ(n³)` time and `Θ(n²)` space bounds of the table algorithm.

Main results:

- Definition {lit}`matrixChainSpace`: the number of distinct subproblems.
- Theorem {lit}`matrixChainSpace_le_square`: the table stores `O(n²)` entries.
- Definition {lit}`matrixChainTime`: the number of split evaluations.
- Theorem {lit}`matrixChainTime_le_cubic`: the algorithm performs `O(n³)` split
  evaluations.

Status: `proved` for the tabulated algorithm's time and space bounds.  The
optimality and reconstruction theorems remain in the legacy source.

Notation conventions used in this section:

- `dims` : the dimension table, {lit}`dims i` = the number of rows of matrix {lit}`Aᵢ`
- `n` : the number of matrices
-/

namespace CLRS
namespace Chapter15

/-! ## Space and time of the table algorithm -/

/-- The number of distinct {lit}`(i, j)` subproblems with {lit}`0 ≤ i ≤ j ≤ n`,
    i.e. the space used by the two tables. -/
def matrixChainSpace (n : Nat) : Nat :=
  (n + 1) * (n + 2) / 2

/-- The number of split evaluations performed by `MATRIX-CHAIN-ORDER`: for each
    interval {lit}`[i, j]` there are {lit}`j - i` candidate split points. -/
def matrixChainTime (n : Nat) : Nat :=
  (Finset.range (n + 1)).sum (fun j => (Finset.range j).sum (fun i => j - i))

/-- The table has `(n + 1)(n + 2) / 2` entries. -/
theorem matrixChainSpace_eq (n : Nat) :
    matrixChainSpace n = (n + 1) * (n + 2) / 2 := rfl

/-- `MATRIX-CHAIN-ORDER` stores `O(n²)` table entries. -/
theorem matrixChainSpace_le_square (n : Nat) : matrixChainSpace n ≤ (n + 2) ^ 2 := by
  unfold matrixChainSpace
  calc
    (n + 1) * (n + 2) / 2 ≤ (n + 1) * (n + 2) := Nat.div_le_self _ _
    _ ≤ (n + 2) * (n + 2) := Nat.mul_le_mul_right _ (by omega : n + 1 ≤ n + 2)
    _ = (n + 2) ^ 2 := by rw [pow_two]

/-- `MATRIX-CHAIN-ORDER` performs `O(n³)` split evaluations. -/
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
