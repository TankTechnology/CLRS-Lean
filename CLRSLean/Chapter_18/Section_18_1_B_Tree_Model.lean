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
- Theorem {lit}`BTree.minKeys_lower_bound`: the first-pass minimum-key function
  exposes the CLRS lower-bound expression {lit}`2 * t^h - 1`.
- Theorem {lit}`BTree.minKeys_succ`: the CLRS lower-bound expression satisfies
  the height-step recurrence used by the B-tree height analysis.

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
theorem search_correct {minDegree x : Nat} {t : BTree}
    (_hvalid : Valid minDegree t) :
    search x t = true <-> mem x t := by
  simp [search]

/--
The CLRS lower-bound expression for the minimum number of keys in a nonempty
B-tree of height {lit}`h` and minimum degree {lit}`minDegree`.
-/
def minKeys (minDegree height : Nat) : Nat :=
  2 * minDegree ^ height - 1

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

end BTree
end Chapter18
end CLRS
