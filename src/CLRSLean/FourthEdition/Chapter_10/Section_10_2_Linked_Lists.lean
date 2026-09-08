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
- Theorem {lit}`listSearch_eq_none_iff`: failure is equivalent to no match.
- Theorems {lit}`listSearch_eq_some_iff_prefix` and
  {lit}`listSearch_eq_some_iff_firstIndex`: success identifies the first match.
- Theorem {lit}`mem_listInsert_self`: inserting at the front makes the inserted
  element a member.
- Theorem {lit}`mem_listDeleteAll_iff`: deleting all nodes with a key gives the
  expected membership characterization.

Status: `proved` for the functional-list model.

Deletion in this model removes every equal value, including duplicates; it
does not represent deletion of one node by pointer identity.

Deferred refinements: pointer updates, identity-based deletion, and free-list allocation.
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


/-- The local executable search is the standard first-match list search. -/
theorem listSearch_eq_find? (p : α → Bool) (xs : List α) :
    listSearch p xs = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x <;> simp [listSearch, ih, hp]

/-- Search fails exactly when every input element fails the predicate. -/
theorem listSearch_eq_none_iff (p : α → Bool) (xs : List α) :
    listSearch p xs = none ↔ ∀ x ∈ xs, p x = false := by
  rw [listSearch_eq_find?, List.find?_eq_none]
  simp

/-- A successful search splits the input at a matching value, with no match
in the preceding prefix. This characterizes the first match even with duplicates. -/
theorem listSearch_eq_some_iff_prefix (p : α → Bool) (xs : List α) (x : α) :
    listSearch p xs = some x ↔ p x = true ∧
      ∃ before after, xs = before ++ x :: after ∧ ∀ y ∈ before, p y = false := by
  rw [listSearch_eq_find?]
  simpa using (List.find?_eq_some_iff_append (xs := xs) (p := p) (b := x))

/-- Search succeeds precisely at a matching index whose earlier positions all
fail the predicate. The index is in range and identifies the returned payload. -/
theorem listSearch_eq_some_iff_firstIndex (p : α → Bool) (xs : List α) (x : α) :
    listSearch p xs = some x ↔ p x = true ∧
      ∃ (i : Nat) (hi : i < xs.length), xs[i] = x ∧
        ∀ j (hj : j < i), p (xs[j]'(Nat.lt_trans hj hi)) = false := by
  rw [listSearch_eq_find?]
  simpa using (List.find?_eq_some_iff_getElem (xs := xs) (p := p) (b := x))

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
