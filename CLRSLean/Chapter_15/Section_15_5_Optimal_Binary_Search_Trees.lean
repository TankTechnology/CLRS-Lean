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

Current gaps:

* Mutable-array memoization and a reconstruction procedure that returns a
  {lit}`BSTPlan` from the filled table remain future refinements.
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
