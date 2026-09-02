import Mathlib

/-!
# CLRS Section 10.2 - Linked lists

This section uses ordinary Lean lists as the mathematical model of a linked
list.  It captures the lookup, front insertion, and deletion-by-key behavior
that CLRS proves informally before one adds pointer fields and memory
allocation.

Main results:

- Theorem {lit}`listSearch_sound`: a successful search returns an element from
  the input list satisfying the predicate.
- Theorem {lit}`mem_listInsert_self`: inserting at the front makes the inserted
  element a member.
- Theorem {lit}`mem_listDeleteAll_iff`: deleting all nodes with a key gives the
  expected membership characterization.

Status: `proved` for the functional-list model.

Deferred refinements: pointer updates and free-list allocation.
-/

namespace CLRS
namespace Chapter10

/-! ## Functional linked-list operations -/

/-- Search a list for the first element satisfying a Boolean predicate. -/
def listSearch (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else listSearch p xs

/-- Insert an element at the head of a linked list. -/
def listInsert (x : α) (xs : List α) : List α :=
  x :: xs

/-- Delete every node whose key equals {lit}`x`. -/
def listDeleteAll [DecidableEq α] (x : α) (xs : List α) : List α :=
  xs.filter fun y => y != x

/-! ## Search correctness -/

/-- A successful search returns a member of the input list satisfying the predicate. -/
theorem listSearch_sound {p : α → Bool} {xs : List α} {x : α}
    (h : listSearch p xs = some x) :
    x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
      simp [listSearch] at h
  | cons y ys ih =>
      by_cases hy : p y = true
      · simp [listSearch, hy] at h
        subst x
        exact ⟨by simp, hy⟩
      · have hyfalse : p y = false := by
          cases hpy : p y <;> simp [hpy] at hy ⊢
        simp [listSearch, hyfalse] at h
        rcases ih h with ⟨hmem, hp⟩
        exact ⟨by simp [hmem], hp⟩

/-! ## Insert and delete correctness -/

/-- The inserted element is a member of the resulting list. -/
theorem mem_listInsert_self (x : α) (xs : List α) :
    x ∈ listInsert x xs := by
  simp [listInsert]

/-- Existing members remain members after front insertion. -/
theorem mem_listInsert_of_mem {x y : α} {xs : List α}
    (h : y ∈ xs) : y ∈ listInsert x xs := by
  simp [listInsert, h]

/-- Delete-all has the expected membership characterization. -/
theorem mem_listDeleteAll_iff [DecidableEq α] {x y : α} {xs : List α} :
    y ∈ listDeleteAll x xs ↔ y ∈ xs ∧ y ≠ x := by
  simp [listDeleteAll]

/-- Deleting all copies of {lit}`x` removes {lit}`x`. -/
theorem not_mem_listDeleteAll_self [DecidableEq α] (x : α) (xs : List α) :
    x ∉ listDeleteAll x xs := by
  simp [listDeleteAll]

end Chapter10
end CLRS
