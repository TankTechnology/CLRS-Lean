import Mathlib

/-!
# CLRS Section 15.2 - Matrix-chain multiplication

This section adds a first mathematical proof layer for matrix-chain
multiplication.  A parenthesization is represented by an inductive
{lit}`ChainPlan i j`, and a candidate dynamic-programming cost table is
specified by the usual split lower bound.  The main theorem says every concrete
parenthesization has cost at least the candidate optimum for its interval.

Current gaps:

* This file proves the optimality interface for a supplied cost table.  It does
  not yet prove a bottom-up table-filling implementation correct.
-/

namespace CLRS
namespace Chapter15

/-! ## Parenthesization model -/

/-- A binary parenthesization of the matrix chain from index {lit}`i` to {lit}`j`. -/
inductive ChainPlan : Nat → Nat → Type where
  | single (i : Nat) : ChainPlan i i
  | split (i k j : Nat) :
      ChainPlan i k → ChainPlan (k + 1) j → ChainPlan i j

namespace ChainPlan

/-- The left endpoint of a chain plan is at most the right endpoint. -/
theorem start_le_end {i j : Nat} (plan : ChainPlan i j) : i ≤ j := by
  induction plan with
  | single i =>
      exact le_rfl
  | split i k j left right ihLeft ihRight =>
      exact Nat.le_trans ihLeft (Nat.le_trans (Nat.le_succ k) ihRight)

/--
The scalar multiplication cost of a parenthesization, using the CLRS dimension
array convention: matrix {lit}`A_i` has dimensions {lit}`dims i` by
{lit}`dims (i+1)`.
-/
def cost (dims : Nat → Nat) : {i j : Nat} → ChainPlan i j → Nat
  | _, _, single _ => 0
  | _, _, split i k j left right =>
      cost dims left + cost dims right + dims i * dims (k + 1) * dims (j + 1)

end ChainPlan

/-! ## Optimality interface -/

/-- The CLRS split cost for multiplying matrices {lit}`i..j` split after {lit}`k`. -/
def matrixSplitCost (dims : Nat → Nat) (opt : Nat → Nat → Nat)
    (i j k : Nat) : Nat :=
  opt i k + opt (k + 1) j + dims i * dims (k + 1) * dims (j + 1)

/--
A candidate cost table satisfies the matrix-chain lower-bound recurrence if
every valid first split has cost at least the table entry.
-/
def MatrixChainLowerBound (dims : Nat → Nat) (opt : Nat → Nat → Nat) : Prop :=
  (∀ i, opt i i = 0) ∧
    ∀ {i j k}, k ∈ Finset.Icc i (j - 1) →
      opt i j ≤ matrixSplitCost dims opt i j k

/--
Every concrete parenthesization has cost at least the candidate optimum
specified by the recurrence lower-bound interface.
-/
theorem matrixChain_opt_le_planCost {dims : Nat → Nat}
    {opt : Nat → Nat → Nat} (hopt : MatrixChainLowerBound dims opt) :
    ∀ {i j : Nat} (plan : ChainPlan i j),
      opt i j ≤ ChainPlan.cost dims plan := by
  intro i j plan
  induction plan with
  | single i =>
      simpa [ChainPlan.cost] using hopt.1 i
  | split i k j left right ihLeft ihRight =>
      have hik : i ≤ k := ChainPlan.start_le_end left
      have hkj : k + 1 ≤ j := ChainPlan.start_le_end right
      have hmem : k ∈ Finset.Icc i (j - 1) := by
        rw [Finset.mem_Icc]
        omega
      have hsplit := hopt.2 hmem
      unfold matrixSplitCost at hsplit
      simp [ChainPlan.cost]
      omega

end Chapter15
end CLRS
