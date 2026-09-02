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
from that split table has exactly the candidate optimal cost, and therefore has
cost no greater than any competing parenthesization.  Any two plans
reconstructed from the same tight split table for the same interval have the
same cost.

Status: `proved` for the mathematical optimal-cost layer, with executable
bottom-up table and optimal parenthesization.

Deferred refinements:

* Mutable-array memoization is a future implementation-level target.
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
Any two parenthesizations reconstructed from the same tight split table for the
same interval have equal cost.
-/
theorem matrixChain_reconstructed_cost_eq_of_reconstructed {dims : Nat → Nat}
    {opt : Nat → Nat → Nat} {splitAt : Nat → Nat → Nat}
    (hsplit : MatrixChainSplitOptimal dims opt splitAt)
    {i j : Nat} {left right : ChainPlan i j}
    (hleft : ChainPlan.ReconstructedBy splitAt left)
    (hright : ChainPlan.ReconstructedBy splitAt right) :
    ChainPlan.cost dims left = ChainPlan.cost dims right := by
  calc
    ChainPlan.cost dims left = opt i j :=
      matrixChain_reconstructed_cost_eq hsplit hleft
    _ = ChainPlan.cost dims right :=
      (matrixChain_reconstructed_cost_eq hsplit hright).symm

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

/--
Direct cost inequality form of the split-table reconstruction theorem: a plan
rebuilt from a tight split table is no more expensive than any other
parenthesization of the same interval.
-/
theorem matrixChain_reconstructed_cost_le_planCost {dims : Nat → Nat}
    {opt : Nat → Nat → Nat} {splitAt : Nat → Nat → Nat}
    (hlower : MatrixChainLowerBound dims opt)
    (hsplit : MatrixChainSplitOptimal dims opt splitAt)
    {i j : Nat} {plan : ChainPlan i j}
    (hrec : ChainPlan.ReconstructedBy splitAt plan)
    (other : ChainPlan i j) :
    ChainPlan.cost dims plan ≤ ChainPlan.cost dims other := by
  exact matrixChain_reconstructed_optimal hlower hsplit hrec other

/-! ## Bottom-up cost table and final optimality -/

def matrixChainOpt (dims : Nat → Nat) : Nat → Nat → Nat
  | i, j =>
      if h : i < j then
        (Finset.Icc i (j - 1)).attach.inf'
          (Finset.attach_nonempty_iff.mpr (by
            use i; simp [Finset.mem_Icc]; omega))
          (fun k =>
            matrixChainOpt dims i k.1 +
            matrixChainOpt dims (k.1 + 1) j +
            dims i * dims (k.1 + 1) * dims (j + 1))
      else
        0
termination_by i j => j - i
decreasing_by
  all_goals
    have hk := Finset.mem_Icc.mp k.2
    omega

theorem matrixChainOpt_lowerBound (dims : Nat → Nat) :
    MatrixChainLowerBound dims (matrixChainOpt dims) := by
  refine ⟨?_, ?_⟩
  · intro i; unfold matrixChainOpt; simp
  · intro i j k hk
    rcases Finset.mem_Icc.mp hk with ⟨hik, hkj⟩
    by_cases hij : i < j
    · unfold matrixChainOpt; simp [hij]
      unfold matrixSplitCost
      have hm : (⟨k, Finset.mem_Icc.mpr ⟨hik, hkj⟩⟩ : {x // x ∈ Finset.Icc i (j - 1)}) ∈
          (Finset.Icc i (j - 1)).attach := by simp
      -- Goal: attach.inf' (fun r => ... r.1 ...) ≤ matrixChainOpt i k + ...
      -- Finset.inf'_le gives: attach.inf' (fun r => ...) ≤ (fun r => ... r.1 ...) ⟨k, ...⟩
      -- After beta reduction, RHS = matrixChainOpt i k + ...
      let f : {x // x ∈ Finset.Icc i (j - 1)} → ℕ :=
        λ r => matrixChainOpt dims i r.1 + matrixChainOpt dims (r.1 + 1) j +
          dims i * dims (r.1 + 1) * dims (j + 1)
      simpa [f] using Finset.inf'_le f hm
    · have hzero : matrixChainOpt dims i j = 0 := by
        unfold matrixChainOpt; simp [hij]
      rw [hzero]
      exact Nat.zero_le _

private lemma bridge_attach_inf (dims : Nat → Nat) (i j : Nat) (hij : i < j) :
    matrixChainOpt dims i j =
    (Finset.Icc i (j - 1)).inf'
      (by use i; simp [Finset.mem_Icc]; omega)
      (λ k => matrixChainOpt dims i k + matrixChainOpt dims (k + 1) j +
        dims i * dims (k + 1) * dims (j + 1)) := by
  let s := Finset.Icc i (j - 1)
  have Hs : s.Nonempty := by use i; simp [s, Finset.mem_Icc]; omega
  let f (k : ℕ) := matrixChainOpt dims i k + matrixChainOpt dims (k + 1) j +
    dims i * dims (k + 1) * dims (j + 1)
  let g (r : {x // x ∈ s}) : ℕ :=
    matrixChainOpt dims i r.1 + matrixChainOpt dims (r.1 + 1) j +
    dims i * dims (r.1 + 1) * dims (j + 1)
  have h1 : matrixChainOpt dims i j = s.attach.inf' (Finset.attach_nonempty_iff.mpr Hs) g := by
    unfold matrixChainOpt; simp [hij, s, g]
  have h2 : s.attach.inf' (Finset.attach_nonempty_iff.mpr Hs) g = s.inf' Hs f := by
    have h_att : s.attach.Nonempty := Finset.attach_nonempty_iff.mpr Hs
    apply le_antisymm
    · -- attach.inf' ≤ inf', via lower bound on inf'
      apply Finset.le_inf' Hs f
      intro x hx
      have hm : (⟨x, hx⟩ : {x // x ∈ s}) ∈ s.attach := by simp
      simpa [f, g] using Finset.inf'_le g hm
    · -- inf' ≤ attach.inf', via lower bound on attach.inf'
      apply Finset.le_inf' h_att g
      intro r hr
      -- r ∈ s.attach, so r.2 : r.1 ∈ s
      simpa [f, g] using Finset.inf'_le f r.2
  rw [h1, h2]

private lemma exists_inf'_eq (s : Finset ℕ) (h : s.Nonempty) (f : ℕ → ℕ) :
    ∃ a ∈ s, f a = s.inf' h f := by
  induction' s using Finset.induction with a s has ih
  · exact absurd h (by simp)
  · by_cases hs : s.Nonempty
    · rcases ih hs with ⟨b, hb, hb_eq⟩
      rw [Finset.inf'_insert hs f]
      by_cases hle : f a ≤ s.inf' hs f
      · rw [min_eq_left hle]
        exact ⟨a, Finset.mem_insert_self a s, rfl⟩
      · rw [min_eq_right (by omega : s.inf' hs f ≤ f a)]
        rw [← hb_eq]
        exact ⟨b, Finset.mem_insert_of_mem hb, rfl⟩
    · have hsingleton : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hsingleton
      simp

/--
The computable split-point selector for matrix-chain DP.  For interval
{lit}`i < j`, it selects the smallest {lit}`k` in {lit}`[i, j-1]` that attains
the minimum split cost.  This makes the entire reconstruction chain computable
without {lit}`Exists.choose`.
-/
def matrixChainSplit (dims : Nat → Nat) (i j : Nat) : Nat :=
  if h : i < j then
    (Finset.Icc i (j - 1)).filter
      (fun k =>
        matrixChainOpt dims i k + matrixChainOpt dims (k + 1) j +
          dims i * dims (k + 1) * dims (j + 1) = matrixChainOpt dims i j) |>.min'
      (by
        have h_nonempty : (Finset.Icc i (j - 1)).Nonempty := by
          use i; simp [Finset.mem_Icc]; omega
        let f (k : ℕ) := matrixChainOpt dims i k + matrixChainOpt dims (k + 1) j +
          dims i * dims (k + 1) * dims (j + 1)
        have h_eq : matrixChainOpt dims i j =
            (Finset.Icc i (j - 1)).inf' h_nonempty f :=
          bridge_attach_inf dims i j h
        have h_exists := exists_inf'_eq (Finset.Icc i (j - 1)) h_nonempty f
        rw [← h_eq] at h_exists
        rcases h_exists with ⟨k, hk, hk_eq⟩
        exact ⟨k, Finset.mem_filter.mpr ⟨hk, hk_eq⟩⟩)
  else
    i

theorem matrixChainSplit_optimal (dims : Nat → Nat) (i j : Nat) (hij : i < j) :
    matrixChainSplit dims i j ∈ Finset.Icc i (j - 1) ∧
    matrixChainOpt dims i j =
      matrixSplitCost dims (matrixChainOpt dims) i j (matrixChainSplit dims i j) := by
  let s : Finset ℕ := Finset.Icc i (j - 1)
  have h_nonempty : s.Nonempty := by use i; simp [s, Finset.mem_Icc]; omega
  let f (k : ℕ) := matrixChainOpt dims i k + matrixChainOpt dims (k + 1) j +
    dims i * dims (k + 1) * dims (j + 1)
  have h_opt_eq : matrixChainOpt dims i j = s.inf' h_nonempty f :=
    bridge_attach_inf dims i j hij
  have h_exists : ∃ k ∈ s, f k = matrixChainOpt dims i j := by
    rw [h_opt_eq]; exact exists_inf'_eq s h_nonempty f
  have h_filter_nonempty : (s.filter fun k => f k = matrixChainOpt dims i j).Nonempty := by
    rcases h_exists with ⟨k, hk, hk_eq⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hk_eq⟩⟩
  set k := (s.filter fun k => f k = matrixChainOpt dims i j).min' h_filter_nonempty with hk_def
  have hk_mem_filter : k ∈ s.filter fun k => f k = matrixChainOpt dims i j := by
    rw [hk_def]; exact Finset.min'_mem _ h_filter_nonempty
  have hk_mem : k ∈ s := (Finset.mem_filter.mp hk_mem_filter).1
  have hk_eq : f k = matrixChainOpt dims i j := (Finset.mem_filter.mp hk_mem_filter).2
  have h_split_val : matrixChainSplit dims i j = k := by
    unfold matrixChainSplit
    simp [hij, s, f, hk_def]
  rw [h_split_val]
  refine ⟨hk_mem, ?_⟩
  unfold matrixSplitCost
  dsimp [f] at hk_eq
  rw [← hk_eq]

theorem matrixChainOpt_splitOptimal (dims : Nat → Nat) :
    MatrixChainSplitOptimal dims (matrixChainOpt dims) (matrixChainSplit dims) := by
  refine ⟨?_, ?_⟩
  · intro i; simp [matrixChainOpt]
  · intro i j hij; exact matrixChainSplit_optimal dims i j hij

def matrixChainReconstruct (dims : Nat → Nat) (i j : Nat) (hbound : i ≤ j) : ChainPlan i j :=
  if h : i < j then
    let k := matrixChainSplit dims i j
    ChainPlan.split i k j
      (matrixChainReconstruct dims i k (by
        have hsplit := matrixChainSplit_optimal dims i j h
        rcases hsplit with ⟨hmem, _⟩
        rcases Finset.mem_Icc.mp hmem with ⟨hlo, hhi⟩
        omega))
      (matrixChainReconstruct dims (k + 1) j (by
        have hsplit := matrixChainSplit_optimal dims i j h
        rcases hsplit with ⟨hmem, _⟩
        rcases Finset.mem_Icc.mp hmem with ⟨hlo, hhi⟩
        omega))
  else
    have heq : i = j := by omega
    heq ▸ ChainPlan.single j
termination_by j - i
decreasing_by
  · have hsplit := matrixChainSplit_optimal dims i j h
    rcases hsplit with ⟨hmem, _⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hlo, _hhi⟩
    omega
  · have hsplit := matrixChainSplit_optimal dims i j h
    rcases hsplit with ⟨hmem, _⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hlo, _hhi⟩
    omega

theorem matrixChainReconstruct_reconstructed (dims : Nat → Nat) (i j : Nat) (hbound : i ≤ j) :
    ChainPlan.ReconstructedBy (matrixChainSplit dims) (matrixChainReconstruct dims i j hbound) := by
  unfold matrixChainReconstruct
  split
  · next h =>
    have hsplit := matrixChainSplit_optimal dims i j h
    rcases hsplit with ⟨hmem, _⟩
    rcases Finset.mem_Icc.mp hmem with ⟨hlo, hhi⟩
    have h_left_bound : i ≤ matrixChainSplit dims i j := by omega
    have h_right_bound : matrixChainSplit dims i j + 1 ≤ j := by omega
    simp
    refine ChainPlan.ReconstructedBy.split i (matrixChainSplit dims i j) j rfl
      (matrixChainReconstruct_reconstructed dims i (matrixChainSplit dims i j) (by omega))
      (matrixChainReconstruct_reconstructed dims (matrixChainSplit dims i j + 1) j (by omega))
  · next h =>
    have heq : i = j := by omega
    cases heq
    exact ChainPlan.ReconstructedBy.single i
termination_by j - i
decreasing_by
  · omega
  · omega

theorem matrixChain_correct (dims : Nat → Nat) (i j : Nat) (hbound : i ≤ j) :
    ∃ plan : ChainPlan i j, MatrixChainOptimalPlan dims plan := by
  let plan := matrixChainReconstruct dims i j hbound
  refine ⟨plan, matrixChain_reconstructed_optimal
    (matrixChainOpt_lowerBound dims)
    (matrixChainOpt_splitOptimal dims)
    (matrixChainReconstruct_reconstructed dims i j hbound)⟩

end Chapter15
end CLRS
