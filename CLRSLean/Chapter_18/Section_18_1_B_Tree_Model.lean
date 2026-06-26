import Mathlib

/-!
# CLRS Section 18.1 - B-tree model

This section introduces a compact mathematical B-tree surface for the first
Chapter 18 pass.  It records key membership, a minimum-degree validity predicate,
search correctness, and the CLRS minimum-key lower-bound expression used by the
height theorem.

Main results:

- Theorem {lit}`BTree.search_correct`: Boolean search is equivalent to key
  membership.
- Theorems {lit}`BTree.search_true_iff`, {lit}`BTree.search_true_of_mem`,
  {lit}`BTree.mem_of_search_true`, {lit}`BTree.search_false_iff`,
  {lit}`BTree.search_false_of_not_mem`, and
  {lit}`BTree.not_mem_of_search_false`: direct success and failure wrappers for
  the Boolean search specification.
- Theorem {lit}`BTree.minKeys_zero`: the CLRS minimum-key expression is one at
  height zero.
- Theorems {lit}`BTree.minKeys_pos` and {lit}`BTree.one_le_minKeys`: for a
  positive minimum degree, the expression is positive and at least one.
- Theorem {lit}`BTree.minKeys_lower_bound`: the first-pass minimum-key function
  exposes the CLRS lower-bound expression {lit}`2 * t^h - 1`.
- Theorem {lit}`BTree.minKeys_succ`: the CLRS lower-bound expression satisfies
  the height-step recurrence used by the B-tree height analysis.
- Theorems {lit}`BTree.minKeys_le_succ` and
  {lit}`BTree.minKeys_monotone_height`: the CLRS lower-bound expression is
  monotone as height increases.

Current gaps:

- Node occupancy, separator ordering, and same-depth leaf invariants are
  represented by the abstract validity predicate only.  They are strengthening
  targets for the full B-tree implementation proof.
-/

namespace CLRS
namespace Chapter18

/-- A first-pass B-tree node stores a list of keys and a list of child trees. -/
inductive BTree where
  | node (keys : List Nat) (children : List BTree) : BTree
  deriving Repr

namespace BTree

/-- Flatten all keys stored in a B-tree. -/
def keysOf : BTree -> List Nat
  | node keys children => keys ++ children.flatMap keysOf

/-- Key membership in the flattened mathematical B-tree model. -/
def mem (x : Nat) (t : BTree) : Prop :=
  x ∈ keysOf t

/-- Membership in the first-pass model is decidable because keys are naturals. -/
instance decidableMem (x : Nat) (t : BTree) : Decidable (mem x t) :=
  inferInstanceAs (Decidable (x ∈ keysOf t))

/--
First-pass validity predicate.  It keeps the CLRS minimum-degree side condition
visible while later refinements add occupancy, separator, and leaf-depth fields.
-/
def Valid (minDegree : Nat) (_t : BTree) : Prop :=
  2 <= minDegree

/-- Boolean B-tree search over the first-pass membership specification. -/
def search (x : Nat) (t : BTree) : Bool :=
  decide (mem x t)

/-- Boolean search succeeds exactly for keys occurring in the tree. -/
theorem search_true_iff (x : Nat) (t : BTree) :
    search x t = true <-> mem x t := by
  simp [search]

/-- Membership implies successful Boolean search. -/
theorem search_true_of_mem (x : Nat) (t : BTree) (hx : mem x t) :
    search x t = true := by
  exact (search_true_iff x t).mpr hx

/-- Successful Boolean search returns a key present in the tree. -/
theorem mem_of_search_true (x : Nat) (t : BTree)
    (hx : search x t = true) :
    mem x t := by
  exact (search_true_iff x t).mp hx

/-- Boolean search fails exactly for keys absent from the tree. -/
theorem search_false_iff (x : Nat) (t : BTree) :
    search x t = false <-> ¬ mem x t := by
  simp [search]

/-- Absence implies failed Boolean search. -/
theorem search_false_of_not_mem (x : Nat) (t : BTree)
    (hx : ¬ mem x t) :
    search x t = false := by
  exact (search_false_iff x t).mpr hx

/-- Failed Boolean search returns a key absent from the tree. -/
theorem not_mem_of_search_false (x : Nat) (t : BTree)
    (hx : search x t = false) :
    ¬ mem x t := by
  exact (search_false_iff x t).mp hx

/-- Boolean search succeeds exactly for keys occurring in the tree. -/
theorem search_correct {minDegree x : Nat} {t : BTree}
    (_hvalid : Valid minDegree t) :
    search x t = true <-> mem x t := by
  exact search_true_iff x t

/--
The CLRS lower-bound expression for the minimum number of keys in a nonempty
B-tree of height {lit}`h` and minimum degree {lit}`minDegree`.
-/
def minKeys (minDegree height : Nat) : Nat :=
  2 * minDegree ^ height - 1

/-- At height zero, the CLRS minimum-key expression is one. -/
theorem minKeys_zero (minDegree : Nat) :
    minKeys minDegree 0 = 1 := by
  simp [minKeys]

/-- With positive minimum degree, the CLRS minimum-key expression is positive. -/
theorem minKeys_pos {minDegree height : Nat} (hdegree : 0 < minDegree) :
    0 < minKeys minDegree height := by
  unfold minKeys
  have hpow : 0 < minDegree ^ height := pow_pos hdegree height
  have hlt : 1 < 2 * minDegree ^ height := by omega
  exact Nat.sub_pos_of_lt hlt

/-- With positive minimum degree, the CLRS minimum-key expression is at least one. -/
theorem one_le_minKeys {minDegree height : Nat} (hdegree : 0 < minDegree) :
    1 <= minKeys minDegree height := by
  exact Nat.succ_le_of_lt
    (minKeys_pos (minDegree := minDegree) (height := height) hdegree)

/-- The first-pass minimum-key function exposes the CLRS lower-bound expression. -/
theorem minKeys_lower_bound {minDegree height : Nat}
    (_hdegree : 2 <= minDegree) :
    2 * minDegree ^ height - 1 <= minKeys minDegree height := by
  rfl

/--
The minimum-key lower-bound expression satisfies the height-step recurrence
{lit}`N(h+1)+1 = t*(N(h)+1)` for valid minimum degree {lit}`t`.
-/
theorem minKeys_succ {minDegree height : Nat}
    (hdegree : 2 <= minDegree) :
    minKeys minDegree (height + 1) + 1 =
      minDegree * (minKeys minDegree height + 1) := by
  unfold minKeys
  have hpos : 0 < minDegree := by omega
  have hpowPos : 0 < minDegree ^ height := pow_pos hpos height
  have htermPos : 0 < 2 * minDegree ^ height :=
    Nat.mul_pos (by decide) hpowPos
  have hnextPowPos : 0 < minDegree ^ (height + 1) :=
    pow_pos hpos (height + 1)
  have hnextTermPos : 0 < 2 * minDegree ^ (height + 1) :=
    Nat.mul_pos (by decide) hnextPowPos
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hnextTermPos)]
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt htermPos)]
  rw [Nat.pow_succ]
  ring

/-- The CLRS minimum-key lower-bound expression is monotone for adjacent heights. -/
theorem minKeys_le_succ {minDegree height : Nat}
    (hdegree : 2 <= minDegree) :
    minKeys minDegree height <= minKeys minDegree (height + 1) := by
  unfold minKeys
  have hpos : 0 < minDegree := by omega
  have hpow : minDegree ^ height <= minDegree ^ (height + 1) := by
    rw [Nat.pow_succ]
    exact Nat.le_mul_of_pos_right (minDegree ^ height) hpos
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hpow) 1

/-- The CLRS minimum-key lower-bound expression is monotone in the height. -/
theorem minKeys_monotone_height {minDegree h₁ h₂ : Nat}
    (hdegree : 2 <= minDegree) (hheight : h₁ <= h₂) :
    minKeys minDegree h₁ <= minKeys minDegree h₂ := by
  induction hheight with
  | refl =>
      rfl
  | step _ ih =>
      exact Nat.le_trans ih (minKeys_le_succ (minDegree := minDegree) hdegree)

end BTree
end Chapter18
end CLRS
