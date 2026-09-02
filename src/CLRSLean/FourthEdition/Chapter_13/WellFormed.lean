import CLRSLean.FourthEdition.Chapter_13.Section_13_4_Deletion

/-!
# Chapter 13 — Bundled red-black-tree correctness

This module packages the structural red-black invariant with binary-search
ordering.  It reuses the native fourth-edition insertion and deletion ordering
theorems, rather than duplicating the older inorder proof development.

Main results:

- Theorem {lit}`wellFormed_insert`: insertion preserves red-black shape and BST
  ordering together.
- Theorem {lit}`wellFormed_delete`: deletion preserves the same bundled
  invariant.
- Theorems {lit}`insert_correct` and {lit}`delete_correct`: invariant and exact
  membership semantics in one client-facing statement.
-/

namespace CLRS
namespace Chapter13
namespace RBTree

/-- A red-black tree is structurally valid and respects binary-search ordering. -/
def WellFormed (t : RBTree) : Prop :=
  RedBlackShape t ∧ BST t

namespace WellFormed

/-- The structural component of a well-formed red-black tree. -/
theorem redBlackShape {t : RBTree} (h : WellFormed t) : RedBlackShape t :=
  h.1

/-- The binary-search-ordering component of a well-formed red-black tree. -/
theorem bst {t : RBTree} (h : WellFormed t) : BST t :=
  h.2

end WellFormed

/-- The empty tree is well formed. -/
theorem wellFormed_empty : WellFormed empty :=
  ⟨redBlackShape_empty, by simp [BST]⟩

/-- Insertion preserves the complete red-black-tree invariant. -/
theorem wellFormed_insert {x : Nat} {t : RBTree} (h : WellFormed t) :
    WellFormed (insert x t) :=
  ⟨redBlackShape_insert h.redBlackShape, bst_insert x h.bst⟩

/-- Deletion preserves the complete red-black-tree invariant. -/
theorem wellFormed_delete {x : Nat} {t : RBTree} (h : WellFormed t) :
    WellFormed (delete x t) :=
  ⟨redBlackShape_delete h.redBlackShape, bst_delete h.bst⟩

/-- Insertion preserves well-formedness and adds exactly the inserted key. -/
theorem insert_correct {x : Nat} {t : RBTree} (h : WellFormed t) :
    WellFormed (insert x t) ∧
      ∀ q, InTree q (insert x t) ↔ q = x ∨ InTree q t :=
  ⟨wellFormed_insert h, fun q => inTree_insert_iff x q t⟩

/-- Deletion preserves well-formedness and removes exactly the deleted key. -/
theorem delete_correct {x : Nat} {t : RBTree} (h : WellFormed t) :
    WellFormed (delete x t) ∧
      ∀ q, InTree q (delete x t) ↔ InTree q t ∧ q ≠ x :=
  ⟨wellFormed_delete h, fun q => inTree_delete_iff x q t h.bst⟩

end RBTree
end Chapter13
end CLRS
