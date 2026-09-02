import Mathlib

/-!
# CLRS Section 15.5 - Optimal binary search trees

This section formalizes the mathematical core of optimal binary search trees.
We use a zero-based internal indexing convention:

* {lit}`BSTPlan i j` with {lit}`i ≤ j` represents a BST containing keys
  {lit}`i+1, ..., j` and dummy keys {lit}`i, ..., j`.
* {lit}`empty i : BSTPlan i i` is the singleton dummy-only tree for dummy key
  {lit}`i`.
* {lit}`node r left right` chooses key {lit}`r` ({lit}`i < r ≤ j`) as the root,
  with left subtree {lit}`BSTPlan i (r-1)` and right subtree {lit}`BSTPlan r j`.

The expected search cost is defined recursively by summing the cost of both
children plus the total weight {lit}`w(i,j)` of the current subtree, because every
search that reaches this subtree pays one extra comparison at its root.

The main results mirror the matrix-chain pattern:

* {lit}`obst_opt_le_planCost`: every concrete BST plan has expected cost at least
  the value prescribed by the OBST recurrence.
* {lit}`obst_reconstructed_cost_eq`: a plan reconstructed from a tight root table
  attains the recurrence value, hence is optimal.
* {lit}`bottomUpOBST_obstRecurrence`: the executable bottom-up table-filling
  function satisfies the CLRS recurrence.

Status: `proved` for the mathematical optimal-cost layer, including executable
bottom-up table and optimal rooted-tree construction.

Deferred refinements:

* Mutable-array memoization is a future implementation-level target.
-/

namespace CLRS
namespace Chapter15
namespace OBST

/-! ## BST plan model and expected cost -/

/--
A BST plan containing keys {lit}`i+1, ..., j` and dummy keys {lit}`i, ..., j`.
{lit}`empty i` is the dummy-only tree for dummy key {lit}`i`.
{lit}`node r left right` has key {lit}`r` as root, with {lit}`i < r ≤ j`.
-/
inductive BSTPlan : Nat → Nat → Type where
  | empty (i : Nat) : BSTPlan i i
  | node {i j : Nat} (r : Nat) :
      i < r → r ≤ j →
      BSTPlan i (r - 1) → BSTPlan r j → BSTPlan i j

namespace BSTPlan

/-- Every valid plan satisfies {lit}`i ≤ j`. -/
theorem start_le_end {i j : Nat} (plan : BSTPlan i j) : i ≤ j := by
  induction plan with
  | empty i => exact le_rfl
  | node r hi _ left _ ihLeft ihRight =>
      exact Nat.le_trans (Nat.le_of_lt hi) ihRight

end BSTPlan

/--
Total weight of the subtree containing keys {lit}`i+1, ..., j` and dummy keys
{lit}`i, ..., j`.  This is the sum of all successful- and unsuccessful-search
probabilities in the subtree.
-/
def weight (p q : Nat → Nat) (i j : Nat) : Nat :=
  (Finset.Icc (i + 1) j).sum p + (Finset.Icc i j).sum q

/--
The expected search cost of a BST plan under success probabilities {lit}`p`
(key {lit}`k` has probability {lit}`p k`) and failure probabilities {lit}`q`
(dummy key {lit}`d_k` has probability {lit}`q k`).
-/
def expectedCost (p q : Nat → Nat) : {i j : Nat} → BSTPlan i j → Nat
  | i, _, BSTPlan.empty _ => q i
  | i, j, BSTPlan.node _ _ _ left right =>
      expectedCost p q left + expectedCost p q right + weight p q i j

/-! ## Recurrence and lower-bound interface -/

/--
A candidate cost table satisfies the OBST lower-bound recurrence:
* singleton dummy intervals have cost at most {lit}`q i`;
* for any admissible root {lit}`r`, the table entry is bounded by the sum of the
  two subproblems plus the subtree weight.
-/
def OBSTLowerBound (p q : Nat → Nat) (opt : Nat → Nat → Nat) : Prop :=
  (∀ i, opt i i ≤ q i) ∧
    ∀ {i j r} (_hij : i < j) (_hr : r ∈ Finset.Icc (i + 1) j),
      opt i j ≤ opt i (r - 1) + opt r j + weight p q i j

/--
A candidate cost table satisfies the exact OBST recurrence:
* singleton dummy intervals have cost exactly {lit}`q i`;
* for {lit}`i < j`, the entry is the minimum over all admissible roots.
-/
def OBSTRecurrence (p q : Nat → Nat) (opt : Nat → Nat → Nat) : Prop :=
  (∀ i, opt i i = q i) ∧
    ∀ {i j} (hij : i < j),
      opt i j = (Finset.Icc (i + 1) j).inf'
        (show (Finset.Icc (i + 1) j).Nonempty from
          ⟨i + 1, by simp [Finset.mem_Icc]; omega⟩)
        (fun r => opt i (r - 1) + opt r j + weight p q i j)

/--
A root table is tight for a candidate cost table when each non-singleton
interval chooses an admissible root that attains the recurrence equality.
-/
def OBSTRootOptimal (p q : Nat → Nat) (opt : Nat → Nat → Nat)
    (rootAt : Nat → Nat → Nat) : Prop :=
  (∀ i, opt i i = q i) ∧
    ∀ {i j} (_hij : i < j),
      rootAt i j ∈ Finset.Icc (i + 1) j ∧
        opt i j = opt i (rootAt i j - 1) + opt (rootAt i j) j + weight p q i j

/--
A concrete BST plan is reconstructed from a root table when every internal
node uses the root index prescribed for its interval.
-/
def ReconstructedBy (rootAt : Nat → Nat → Nat) : {i j : Nat} → BSTPlan i j → Prop
  | _, _, BSTPlan.empty _ => True
  | i, j, BSTPlan.node r _ _ left right =>
      r = rootAt i j ∧ ReconstructedBy rootAt left ∧ ReconstructedBy rootAt right

/-! ## Optimality theorems -/

/-- Every concrete plan costs at least the recurrence lower bound. -/
theorem obst_opt_le_planCost {p q : Nat → Nat} {opt : Nat → Nat → Nat}
    (hopt : OBSTLowerBound p q opt) :
    ∀ {i j : Nat} (plan : BSTPlan i j), opt i j ≤ expectedCost p q plan := by
  intro i j plan
  induction plan with
  | empty i =>
      simpa [expectedCost] using hopt.1 i
  | node r hi hj left right ihLeft ihRight =>
      have h := hopt.2 (Nat.lt_of_lt_of_le hi hj)
        (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hi, hj⟩)
      simp [expectedCost]
      linarith

/-- A plan reconstructed from a tight root table attains the optimum. -/
theorem obst_reconstructed_cost_eq {p q : Nat → Nat} {opt : Nat → Nat → Nat}
    {rootAt : Nat → Nat → Nat} (hroot : OBSTRootOptimal p q opt rootAt) :
    ∀ {i j : Nat} (plan : BSTPlan i j),
      ReconstructedBy rootAt plan → expectedCost p q plan = opt i j := by
  intro i j plan hrec
  induction plan with
  | empty i =>
      simpa [expectedCost] using (hroot.1 i).symm
  | node r hi hj left right ihLeft ihRight =>
      rcases hrec with ⟨hr, hrecLeft, hrecRight⟩
      have h := (hroot.2 (Nat.lt_of_lt_of_le hi hj)).2
      simp [expectedCost, h] at ⊢
      rw [ihLeft hrecLeft, ihRight hrecRight]
      rw [hr]

/-- A reconstructed plan is optimal among all plans for the same interval. -/
theorem obst_reconstructed_optimal {p q : Nat → Nat} {opt : Nat → Nat → Nat}
    {rootAt : Nat → Nat → Nat} (hrec : OBSTRecurrence p q opt)
    (hroot : OBSTRootOptimal p q opt rootAt) {i j : Nat} {plan : BSTPlan i j}
    (hplan : ReconstructedBy rootAt plan) :
    ∀ other : BSTPlan i j,
      expectedCost p q plan ≤ expectedCost p q other := by
  intro other
  have hlb : OBSTLowerBound p q opt := by
    constructor
    · intro i; rw [hrec.1 i]
    · intro i j r hij hr
      rw [(hrec.2 hij)]
      exact Finset.inf'_le _ hr
  have heq := obst_reconstructed_cost_eq hroot plan hplan
  rw [heq]
  exact obst_opt_le_planCost hlb other

/-! ## Executable bottom-up table -/

/--
The canonical executable OBST value function obtained by recursively evaluating
the CLRS recurrence.  The recursion is over the interval length {lit}`j - i`.
-/
def bottomUpOBST (p q : Nat → Nat) : Nat → Nat → Nat
  | i, j =>
      if h : i < j then
        (Finset.Icc (i + 1) j).attach.inf'
          (Finset.attach_nonempty_iff.mpr
            (by use i + 1; simp [Finset.mem_Icc]; exact h))
          (fun r =>
            bottomUpOBST p q i (r.1 - 1) +
              bottomUpOBST p q r.1 j +
              weight p q i j)
      else
        q i
termination_by i j => j - i
decreasing_by
  all_goals
    have hr := Finset.mem_Icc.mp r.2
    omega

/-- The executable bottom-up function satisfies the OBST recurrence. -/
theorem bottomUpOBST_obstRecurrence (p q : Nat → Nat) :
    OBSTRecurrence p q (bottomUpOBST p q) := by
  constructor
  · intro i
    rw [bottomUpOBST]
    simp
  · intro i j hij
    have H : (Finset.Icc (i + 1) j).Nonempty := by
      use i + 1
      simp [Finset.mem_Icc]
      exact hij
    rw [bottomUpOBST]
    simp [hij]
    apply le_antisymm
    · -- The attached inf is a lower bound for every value taken on `Finset.Icc`.
      apply Finset.le_inf' H
        (fun x => bottomUpOBST p q i (x - 1) + bottomUpOBST p q x j + weight p q i j)
      intro x hx
      exact Finset.inf'_le _ (Finset.mem_attach _ ⟨x, hx⟩)
    · -- The plain inf is a lower bound for every value taken on `Finset.attach`.
      apply Finset.le_inf' (Finset.attach_nonempty_iff.mpr H)
        (fun r : {r // r ∈ Finset.Icc (i + 1) j} =>
          bottomUpOBST p q i (r.1 - 1) + bottomUpOBST p q r.1 j + weight p q i j)
      intro r hr
      exact Finset.inf'_le _ r.2

/-! ## Optimal root existence and final correctness -/

open Finset

private lemma exists_inf'_eq (s : Finset ℕ) (h : s.Nonempty) (f : ℕ → ℕ) :
    ∃ a ∈ s, f a = s.inf' h f := by
  induction' s using Finset.induction with a s has ih
  · exact absurd h (by simp)
  · by_cases hs : s.Nonempty
    · rcases ih hs with ⟨b, hb, hb_eq⟩
      rw [Finset.inf'_insert hs f]
      by_cases hle : f a ≤ s.inf' hs f
      · rw [min_eq_left hle]
        exact ⟨a, mem_insert_self a s, rfl⟩
      · rw [min_eq_right (by omega : s.inf' hs f ≤ f a)]
        rw [← hb_eq]
        exact ⟨b, mem_insert_of_mem hb, rfl⟩
    · have hsingleton : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hsingleton
      simp

/--
There exists a tight root table for {name}`bottomUpOBST`.  The proof uses
`Classical.choice` together with {name}`exists_inf'_eq`.
-/
theorem exists_obstRootOptimal (p q : Nat → Nat) :
    ∃ rootAt : Nat → Nat → Nat,
      OBSTRootOptimal p q (bottomUpOBST p q) rootAt := by
  have h_rec : OBSTRecurrence p q (bottomUpOBST p q) :=
    bottomUpOBST_obstRecurrence p q
  have h_diag : ∀ i, bottomUpOBST p q i i = q i := h_rec.1
  have h_exists_root (i j : Nat) (hij : i < j) : ∃ r, r ∈ Finset.Icc (i + 1) j ∧
      bottomUpOBST p q i j =
        bottomUpOBST p q i (r - 1) + bottomUpOBST p q r j + weight p q i j := by
    rw [h_rec.2 hij]
    let s := Finset.Icc (i + 1) j
    have h_nonempty : s.Nonempty := by
      use i + 1; simp [s, Finset.mem_Icc]; omega
    let f (r : ℕ) := bottomUpOBST p q i (r - 1) + bottomUpOBST p q r j + weight p q i j
    rcases exists_inf'_eq s h_nonempty f with ⟨r, hr, heq⟩
    exact ⟨r, hr, heq.symm⟩
  -- Build rootAt pointwise using Exists.choose
  let rootAt (i j : Nat) : Nat :=
    if h : i < j then Exists.choose (h_exists_root i j h) else i
  refine ⟨rootAt, h_diag, ?_⟩
  intro i j hij
  have h_rootAt : rootAt i j = Exists.choose (h_exists_root i j hij) := by
    unfold rootAt; simp [hij]
  rw [h_rootAt]
  exact Exists.choose_spec (h_exists_root i j hij)

/--
Construct a {name}`BSTPlan` recursively following a tight root table.
-/
private def obstBuildPlan (rootAt : Nat → Nat → Nat)
    (hroot : OBSTRootOptimal p q (bottomUpOBST p q) rootAt) (i j : Nat) (hij : i ≤ j) :
    BSTPlan i j :=
  if h : i < j then
    have hmem := Finset.mem_Icc.mp (hroot.2 h).1
    have h_lt_r : i < rootAt i j := by omega
    have h_left_bound : i ≤ rootAt i j - 1 := by omega
    BSTPlan.node (rootAt i j) h_lt_r hmem.2
      (obstBuildPlan rootAt hroot i (rootAt i j - 1) h_left_bound)
      (obstBuildPlan rootAt hroot (rootAt i j) j hmem.2)
  else
    have heq : i = j := by omega
    heq ▸ BSTPlan.empty j
termination_by j - i
decreasing_by
  · -- first recursive call: (rootAt i j - 1) - i < j - i
    have hhi : rootAt i j ≤ j := (Finset.mem_Icc.mp (hroot.2 h).1).2
    omega
  · -- second recursive call: j - rootAt i j < j - i
    have hlo : i + 1 ≤ rootAt i j := (Finset.mem_Icc.mp (hroot.2 h).1).1
    omega

/--
The plan built by {name}`obstBuildPlan` follows the root table.
-/
private theorem obstBuildPlan_reconstructed (rootAt : Nat → Nat → Nat)
    (hroot : OBSTRootOptimal p q (bottomUpOBST p q) rootAt) (i j : Nat) (hij : i ≤ j) :
    ReconstructedBy rootAt (obstBuildPlan rootAt hroot i j hij) := by
  unfold obstBuildPlan
  split
  · next h =>
    have hmem := Finset.mem_Icc.mp (hroot.2 h).1
    have h_left_bound : i ≤ rootAt i j - 1 := by omega
    have h_lt : (rootAt i j - 1) - i < j - i := by
      have hhi : rootAt i j ≤ j := hmem.2
      omega
    have h_rt : j - (rootAt i j) < j - i := by
      have hlo : i + 1 ≤ rootAt i j := hmem.1
      omega
    simp
    exact ⟨rfl,
      obstBuildPlan_reconstructed rootAt hroot i (rootAt i j - 1) h_left_bound,
      obstBuildPlan_reconstructed rootAt hroot (rootAt i j) j hmem.2⟩
  · next h =>
    have heq : i = j := by omega
    subst heq
    simp [ReconstructedBy]
termination_by j - i
decreasing_by
  exact h_lt
  exact h_rt

/--
**Theorem (Optimal BST).**  For any interval {lit}`[i,j]` with {lit}`i ≤ j`,
there exists a binary search tree plan that minimizes expected search cost.
This corresponds to CLRS Theorem 15.7.
-/
theorem obst_correct (p q : Nat → Nat) (i j : Nat) (hij : i ≤ j) :
    ∃ plan : BSTPlan i j,
      ∀ other : BSTPlan i j,
        expectedCost p q plan ≤ expectedCost p q other := by
  rcases exists_obstRootOptimal p q with ⟨rootAt, hroot⟩
  have hrec : OBSTRecurrence p q (bottomUpOBST p q) :=
    bottomUpOBST_obstRecurrence p q
  let plan := obstBuildPlan rootAt hroot i j hij
  refine ⟨plan, λ other => ?_⟩
  have hplan : ReconstructedBy rootAt plan :=
    obstBuildPlan_reconstructed rootAt hroot i j hij
  exact obst_reconstructed_optimal hrec hroot hplan other
