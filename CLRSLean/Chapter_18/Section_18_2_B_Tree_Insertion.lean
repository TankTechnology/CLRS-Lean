import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.2 - B-tree insertion

This first-pass section gives specification-level split and insertion wrappers
over the mathematical B-tree model from Section 18.1.  The goal is a stable
public theorem surface before introducing full node occupancy and separator
repair proofs.

Main results:

- Theorem {lit}`BTree.splitChild_preserves_model`: the first-pass split wrapper
  preserves validity and membership.
- Theorem {lit}`BTree.splitChild_mem_iff`: membership after the first-pass
  split wrapper is unchanged.
- Theorem {lit}`BTree.splitChild_search_iff`: searching after the first-pass
  split wrapper is equivalent to searching before it.
- Theorem {lit}`BTree.insert_preserves_model`: specification insertion preserves
  the first-pass validity predicate.
- Theorem {lit}`BTree.insert_mem_iff`: insertion adds exactly the inserted key
  to the membership specification.
- Theorem {lit}`BTree.insert_search_iff`: searching after insertion succeeds
  exactly for the inserted key or an old searchable key.
- Theorems {lit}`BTree.insert_mem_self` and
  {lit}`BTree.insert_search_self`: the inserted key is present and searchable
  after insertion.
- Theorems {lit}`BTree.insert_mem_old` and
  {lit}`BTree.insert_search_old`: old members and searchable keys remain so
  after insertion.

Current gaps:

- This is not yet the full CLRS in-node split and insert-nonfull proof.  It is a
  specification layer that fixes the public theorem names and membership
  behavior for the later structural refinement.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-- First-pass split-child wrapper.  Structural split refinement is future work. -/
def splitChild (t : BTree) : BTree :=
  t

/-- Membership after the first-pass split wrapper is unchanged. -/
theorem splitChild_mem_iff (x : Nat) (t : BTree) :
    mem x (splitChild t) <-> mem x t := by
  rfl

/-- The first-pass split wrapper preserves validity and membership. -/
theorem splitChild_preserves_model {minDegree : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (splitChild t) ∧
      forall x, mem x (splitChild t) <-> mem x t := by
  exact ⟨hvalid, by intro x; exact splitChild_mem_iff x t⟩

/-- Searching after the first-pass split wrapper is unchanged. -/
theorem splitChild_search_iff {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search x (splitChild t) = true <-> search x t = true := by
  have hsplit := splitChild_preserves_model (minDegree := minDegree) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := x) (t := splitChild t) hsplit.1]
  rw [hsplit.2 x]
  rw [← search_correct (minDegree := minDegree) (x := x) (t := t) hvalid]

/-- Specification-level B-tree insertion: add the key at a fresh root. -/
def insert (x : Nat) (t : BTree) : BTree :=
  node (x :: keysOf t) []

/-- Specification insertion preserves the first-pass validity predicate. -/
theorem insert_preserves_model {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (insert x t) := by
  exact hvalid

/-- Specification insertion adds exactly the inserted key to membership. -/
theorem insert_mem_iff (x y : Nat) (t : BTree) :
    mem y (insert x t) <-> y = x ∨ mem y t := by
  simp [insert, mem, keysOf]

/-- The inserted key is present after specification insertion. -/
theorem insert_mem_self (x : Nat) (t : BTree) :
    mem x (insert x t) := by
  rw [insert_mem_iff]
  exact Or.inl rfl

/-- Old keys remain present after specification insertion. -/
theorem insert_mem_old (x y : Nat) (t : BTree) (hy : mem y t) :
    mem y (insert x t) := by
  rw [insert_mem_iff]
  exact Or.inr hy

/-- Searching after insertion succeeds exactly for the new key or an old key. -/
theorem insert_search_iff {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (insert x t) = true <-> y = x ∨ search y t = true := by
  have hinsert : Valid minDegree (insert x t) :=
    insert_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := y) (t := insert x t) hinsert]
  rw [insert_mem_iff]
  rw [← search_correct (minDegree := minDegree) (x := y) (t := t) hvalid]

/-- Searching for the inserted key succeeds after specification insertion. -/
theorem insert_search_self {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search x (insert x t) = true := by
  have hinsert : Valid minDegree (insert x t) :=
    insert_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := x) (t := insert x t) hinsert]
  exact insert_mem_self x t

/-- Old searchable keys remain searchable after specification insertion. -/
theorem insert_search_old {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hy : search y t = true) :
    search y (insert x t) = true := by
  rw [insert_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact Or.inr hy

end BTree
end Chapter18
end CLRS
