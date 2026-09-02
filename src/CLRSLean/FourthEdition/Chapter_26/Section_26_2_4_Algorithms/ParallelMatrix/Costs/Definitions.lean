import Mathlib.Tactic

/-!
# CLRS Section 26.2 — Exact Costs of Parallel Matrix Algorithms

This module defines the exact work and span recurrences induced by the
executable {lit}`P-ADD` and {lit}`P-MATMUL` implementations.  Their base cases
charge one scalar operation.  Recursive cases include the balanced fork/join
costs recorded by {lit}`Costed.par4` and {lit}`Costed.par8`.

The names {lit}`pMatMulExecWork` and {lit}`pMatMulExecSpan` deliberately
distinguish these execution-attached costs from the earlier idealized
recurrence model.
-/

namespace CLRS
namespace Chapter27

/-! ## P-ADD costs -/

/-- Exact work recurrence induced by the balanced executable {lit}`P-ADD`. -/
def pAddWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    1
  else
    4 * pAddWork (n / 2) + 3
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

/-- Unfold the recursive branch of the exact {lit}`P-ADD` work recurrence. -/
@[simp] theorem pAddWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    pAddWork n = 4 * pAddWork (n / 2) + 3 := by
  rw [pAddWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span recurrence induced by the balanced executable {lit}`P-ADD`. -/
def pAddSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    1
  else
    pAddSpan (n / 2) + 2
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

/-- Unfold the recursive branch of the exact {lit}`P-ADD` span recurrence. -/
@[simp] theorem pAddSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    pAddSpan n = pAddSpan (n / 2) + 2 := by
  rw [pAddSpan]
  simp [show ¬n ≤ 1 by omega]

/-! ## P-MATMUL execution costs -/

/-- Exact work recurrence induced by executable {lit}`P-MATMUL`.

The recursive products contribute the eight-way parallel cost; the final term
is the exact work of the subsequent {lit}`P-ADD` call.
-/
def pMatMulExecWork (n : ℕ) : ℕ :=
  if n ≤ 1 then
    1
  else
    8 * pMatMulExecWork (n / 2) + 7 + pAddWork n
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

/-- Unfold the recursive branch of executable {lit}`P-MATMUL` work. -/
@[simp] theorem pMatMulExecWork_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMatMulExecWork n =
      8 * pMatMulExecWork (n / 2) + 7 + pAddWork n := by
  rw [pMatMulExecWork]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span recurrence induced by executable {lit}`P-MATMUL`.

The eight recursive products run in parallel, after which {lit}`P-ADD` runs
sequentially on their two temporary matrices.
-/
def pMatMulExecSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then
    1
  else
    pMatMulExecSpan (n / 2) + 3 + pAddSpan n
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

/-- Unfold the recursive branch of executable {lit}`P-MATMUL` span. -/
@[simp] theorem pMatMulExecSpan_unfold {n : ℕ} (hn : 2 ≤ n) :
    pMatMulExecSpan n =
      pMatMulExecSpan (n / 2) + 3 + pAddSpan n := by
  rw [pMatMulExecSpan]
  simp [show ¬n ≤ 1 by omega]

end Chapter27
end CLRS
