import Mathlib

/-!
# CLRS Section 12.1 - Binary search trees

This section gives a first Lean model of binary search trees as inductive trees
of natural-number keys.  It proves the fundamental insertion facts used by the
textbook invariant argument: insertion adds exactly the inserted key to the
membership set, and insertion preserves the BST ordering invariant.

Main results:

- Theorem {lit}`inTree_insert_iff`: membership after insertion is exactly the
  old membership relation plus the inserted key.
- Theorem {lit}`insert_ordered`: insertion preserves the BST ordering invariant.

Current gaps:

- Search, minimum/maximum, successor/predecessor, and deletion are future
  section targets.
-/

namespace CLRS
namespace Chapter12

/-! ## Tree model and invariant -/

/-- A binary tree of natural-number keys. -/
inductive BSTree where
  | empty : BSTree
  | node : BSTree → Nat → BSTree → BSTree
  deriving Repr, DecidableEq

namespace BSTree

/-- Membership of a key in a binary tree. -/
def InTree (x : Nat) : BSTree → Prop
  | empty => False
  | node left key right => x = key ∨ InTree x left ∨ InTree x right

/-- Every key in the tree is strictly less than `bound`. -/
def AllLt (bound : Nat) (t : BSTree) : Prop :=
  ∀ x, InTree x t → x < bound

/-- Every key in the tree is strictly greater than `bound`. -/
def AllGt (bound : Nat) (t : BSTree) : Prop :=
  ∀ x, InTree x t → bound < x

/-- The binary-search-tree ordering invariant. -/
def Ordered : BSTree → Prop
  | empty => True
  | node left key right =>
      Ordered left ∧ Ordered right ∧ AllLt key left ∧ AllGt key right

/-- Functional insertion into a binary search tree. -/
def insert (x : Nat) : BSTree → BSTree
  | empty => node empty x empty
  | node left key right =>
      if x < key then
        node (insert x left) key right
      else if key < x then
        node left key (insert x right)
      else
        node left key right

/-! ## Membership after insertion -/

/-- Insertion adds exactly the inserted key to the tree membership relation. -/
theorem inTree_insert_iff (x y : Nat) (t : BSTree) :
    InTree y (insert x t) ↔ y = x ∨ InTree y t := by
  induction t with
  | empty =>
      simp [insert, InTree]
  | node left key right ihLeft ihRight =>
      by_cases hxkey : x < key
      · simp [insert, InTree, hxkey, ihLeft, or_assoc, or_left_comm]
      · by_cases hkeyx : key < x
        · simp [insert, InTree, hxkey, hkeyx, ihRight, or_left_comm]
        · have hxeq : x = key := by
            exact Nat.le_antisymm (Nat.le_of_not_gt hkeyx) (Nat.le_of_not_gt hxkey)
          subst x
          simp [insert, InTree]

/-- The inserted key is a member of the resulting tree. -/
theorem inTree_insert_self (x : Nat) (t : BSTree) :
    InTree x (insert x t) := by
  exact (inTree_insert_iff x x t).mpr (Or.inl rfl)

/-- Existing members remain members after insertion. -/
theorem inTree_insert_of_inTree {x y : Nat} {t : BSTree}
    (h : InTree y t) : InTree y (insert x t) := by
  exact (inTree_insert_iff x y t).mpr (Or.inr h)

/-! ## Ordering after insertion -/

/-- Insertion preserves an upper-bound invariant when the inserted key satisfies it. -/
theorem allLt_insert {x bound : Nat} {t : BSTree}
    (hx : x < bound) (ht : AllLt bound t) :
    AllLt bound (insert x t) := by
  intro y hy
  rcases (inTree_insert_iff x y t).mp hy with rfl | hyold
  · exact hx
  · exact ht y hyold

/-- Insertion preserves a lower-bound invariant when the inserted key satisfies it. -/
theorem allGt_insert {x bound : Nat} {t : BSTree}
    (hx : bound < x) (ht : AllGt bound t) :
    AllGt bound (insert x t) := by
  intro y hy
  rcases (inTree_insert_iff x y t).mp hy with rfl | hyold
  · exact hx
  · exact ht y hyold

/-- Functional BST insertion preserves the binary-search-tree ordering invariant. -/
theorem insert_ordered {x : Nat} {t : BSTree}
    (ht : Ordered t) : Ordered (insert x t) := by
  induction t with
  | empty =>
      simp [insert, Ordered, AllLt, AllGt, InTree]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x < key
      · simp [insert, Ordered, hxkey]
        exact ⟨ihLeft hLeft, hRight, allLt_insert hxkey hLt, hGt⟩
      · by_cases hkeyx : key < x
        · simp [insert, Ordered, hxkey, hkeyx]
          exact ⟨hLeft, ihRight hRight, hLt, allGt_insert hkeyx hGt⟩
        · simp [insert, Ordered, hxkey, hkeyx, hLeft, hRight, hLt, hGt]

end BSTree

end Chapter12
end CLRS
