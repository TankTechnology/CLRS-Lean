import Mathlib

/-!
# CLRS Section 2.1 - Insertion sort

This file is the first Chapter 2 workflow slice.  It formalizes a functional
version of insertion sort and proves the two correctness facts that correspond
to the textbook argument:

* the result is ordered;
* the result is a permutation of the input.

The CLRS pseudocode is array-based and is usually justified by a loop invariant.
Here we use a recursive list algorithm, because it exposes the same invariant as
small structural lemmas: inserting into an ordered list keeps it ordered, and it
does not change the multiset of elements.
-/

namespace CLRS
namespace Chapter02

/-- Every element of {lit}`xs` is at least {lit}`lower`. -/
def AllLe (lower : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, lower ≤ x

/-- A compact sortedness predicate for lists of natural numbers. -/
def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x ≤ y ∧ Ordered (y :: ys)

/-- Insert an element into an already ordered list. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
      if x ≤ y then
        x :: y :: ys
      else
        y :: insertSorted x ys

/-- Functional insertion sort over lists. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (insertionSort xs)

theorem ordered_tail {x : Nat} {xs : List Nat}
    (h : Ordered (x :: xs)) : Ordered xs := by
  cases xs with
  | nil =>
      trivial
  | cons y ys =>
      exact h.2

theorem ordered_allLe_tail {x : Nat} {xs : List Nat}
    (h : Ordered (x :: xs)) : AllLe x xs := by
  induction xs generalizing x with
  | nil =>
      intro y hy
      simp at hy
  | cons y ys ih =>
      intro z hz
      simp at hz
      rcases hz with rfl | hz
      · exact h.1
      · exact Nat.le_trans h.1 (ih h.2 z hz)

theorem ordered_cons_of_allLe {x : Nat} {xs : List Nat}
    (hxs : Ordered xs) (hall : AllLe x xs) : Ordered (x :: xs) := by
  cases xs with
  | nil =>
      trivial
  | cons y ys =>
      exact ⟨hall y (by simp), hxs⟩

theorem allLe_insertSorted {lower x : Nat} {xs : List Nat}
    (hx : lower ≤ x) (hxs : AllLe lower xs) :
    AllLe lower (insertSorted x xs) := by
  induction xs with
  | nil =>
      simpa [AllLe, insertSorted] using hx
  | cons head tail ih =>
      by_cases hxhead : x ≤ head
      · simp [AllLe, insertSorted, hxhead] at hxs ⊢
        exact ⟨hx, hxs⟩
      · simp [AllLe, insertSorted, hxhead] at hxs ⊢
        exact ⟨hxs.1, ih hxs.2⟩

/-- Inserting into an ordered list keeps it ordered. -/
theorem insertSorted_ordered {x : Nat} {xs : List Nat}
    (hxs : Ordered xs) : Ordered (insertSorted x xs) := by
  induction xs with
  | nil =>
      trivial
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simpa [insertSorted, hxy, Ordered] using
          (And.intro hxy hxs : x ≤ y ∧ Ordered (y :: ys))
      · have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_ge hxy)
        have htail : Ordered ys := ordered_tail hxs
        have hordered_insert : Ordered (insertSorted x ys) := ih htail
        have hall_tail : AllLe y ys := ordered_allLe_tail hxs
        have hall_insert : AllLe y (insertSorted x ys) :=
          allLe_insertSorted hyx hall_tail
        simpa [insertSorted, hxy] using
          ordered_cons_of_allLe hordered_insert hall_insert

/-- Inserting into a list preserves the input elements up to permutation. -/
theorem insertSorted_perm (x : Nat) (xs : List Nat) :
    (insertSorted x xs).Perm (x :: xs) := by
  induction xs with
  | nil =>
      simp [insertSorted]
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simp [insertSorted, hxy]
      · simpa [insertSorted, hxy] using
          (List.Perm.cons y ih).trans (List.Perm.swap y x ys).symm

/-- Insertion sort returns an ordered list. -/
theorem insertionSort_sorted (xs : List Nat) : Ordered (insertionSort xs) := by
  induction xs with
  | nil =>
      trivial
  | cons x xs ih =>
      exact insertSorted_ordered ih

/-- Insertion sort preserves the input elements up to permutation. -/
theorem insertionSort_perm (xs : List Nat) :
    (insertionSort xs).Perm xs := by
  induction xs with
  | nil =>
      simp [insertionSort]
  | cons x xs ih =>
      exact (insertSorted_perm x (insertionSort xs)).trans (List.Perm.cons x ih)

end Chapter02
end CLRS
