import Mathlib

/-!
# CLRS Section 15.2 - Matrix-chain multiplication

This section adds a first mathematical proof layer for matrix-chain
multiplication.  A parenthesization is represented by an inductive
{lit}`ChainPlan i j`, and a candidate dynamic-programming cost table is
specified by the usual split lower bound.  The main theorem says every concrete
parenthesization has cost at least the candidate optimum for its interval.
The file also adds a reconstruction certificate: if a split table records a
tight split for each nonsingleton interval, then any parenthesization rebuilt
from that split table has exactly the candidate optimal cost.

Current gaps:

* This file proves the optimality and reconstruction interfaces for supplied
  cost and split tables.  It does not yet prove a bottom-up table-filling
  implementation correct.
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

/--
A parenthesization is reconstructed from a split table when every internal
node uses the split index prescribed for its interval.
-/
inductive ReconstructedBy (splitAt : Nat → Nat → Nat) :
    {i j : Nat} → ChainPlan i j → Prop where
  | single (i : Nat) : ReconstructedBy splitAt (single i)
  | split (i k j : Nat) {left : ChainPlan i k}
      {right : ChainPlan (k + 1) j} :
      k = splitAt i j →
      ReconstructedBy splitAt left →
      ReconstructedBy splitAt right →
      ReconstructedBy splitAt (ChainPlan.split i k j left right)

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
A split table is tight for a candidate matrix-chain cost table when each
nonsingleton interval chooses a valid first split whose split cost is exactly
the table entry.
-/
def MatrixChainSplitOptimal (dims : Nat → Nat) (opt : Nat → Nat → Nat)
    (splitAt : Nat → Nat → Nat) : Prop :=
  (∀ i, opt i i = 0) ∧
    ∀ {i j}, i < j →
      splitAt i j ∈ Finset.Icc i (j - 1) ∧
        opt i j = matrixSplitCost dims opt i j (splitAt i j)

/-- A concrete parenthesization is optimal when no other plan has lower cost. -/
def MatrixChainOptimalPlan (dims : Nat → Nat)
    {i j : Nat} (plan : ChainPlan i j) : Prop :=
  ∀ other : ChainPlan i j, ChainPlan.cost dims plan ≤ ChainPlan.cost dims other

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

/--
Any plan reconstructed from a tight split table has exactly the candidate
optimal cost.
-/
theorem matrixChain_reconstructed_cost_eq {dims : Nat → Nat}
    {opt : Nat → Nat → Nat} {splitAt : Nat → Nat → Nat}
    (hsplit : MatrixChainSplitOptimal dims opt splitAt) :
    ∀ {i j : Nat} {plan : ChainPlan i j},
      ChainPlan.ReconstructedBy splitAt plan →
        ChainPlan.cost dims plan = opt i j := by
  intro i j plan hrec
  induction hrec with
  | single i =>
      simpa [ChainPlan.cost] using (hsplit.1 i).symm
  | split =>
      rename_i i k j left right hk _hleft _hright ihLeft ihRight
      subst k
      have hij : i < j := by
        have hleftLe : i ≤ splitAt i j := ChainPlan.start_le_end left
        have hrightLe : splitAt i j + 1 ≤ j := ChainPlan.start_le_end right
        omega
      rcases hsplit.2 hij with ⟨_hmem, hcost⟩
      simp [ChainPlan.cost, matrixSplitCost, ihLeft, ihRight, hcost]

/--
Combining a lower-bound table with a tight split-table reconstruction proves
the reconstructed parenthesization is globally optimal.
-/
theorem matrixChain_reconstructed_optimal {dims : Nat → Nat}
    {opt : Nat → Nat → Nat} {splitAt : Nat → Nat → Nat}
    (hlower : MatrixChainLowerBound dims opt)
    (hsplit : MatrixChainSplitOptimal dims opt splitAt)
    {i j : Nat} {plan : ChainPlan i j}
    (hrec : ChainPlan.ReconstructedBy splitAt plan) :
    MatrixChainOptimalPlan dims plan := by
  intro other
  have hcost :
      ChainPlan.cost dims plan = opt i j :=
    matrixChain_reconstructed_cost_eq hsplit hrec
  have hother :
      opt i j ≤ ChainPlan.cost dims other :=
    matrixChain_opt_le_planCost hlower other
  omega

end Chapter15
end CLRS
