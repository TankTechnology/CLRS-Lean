import Mathlib

/-!
# CLRS Section 7.1 - Description of quicksort

This file starts the Chapter 7 sorting track with a Lean-friendly functional
model of quicksort.  The CLRS in-place partition procedure is represented by a
stable partition around a pivot; the current theorem layer proves the same
mathematical facts used by the textbook proof:

* partition returns exactly the original tail elements;
* the left partition contains only elements at most the pivot;
* the right partition contains only elements greater than the pivot;
* functional quicksort returns an ordered permutation of the input.

The in-place array partition loop and the randomized/expected-time analysis are
separate strengthening targets.
-/

namespace CLRS
namespace Chapter07

/-! ## Ordered lists and pivot bounds -/

/-- A compact sortedness predicate for lists of natural numbers. -/
def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x ≤ y ∧ Ordered (y :: ys)

/-- Every element of {lit}`xs` is at least {lit}`lower`. -/
def AllLe (lower : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, lower ≤ x

/-- Every element of {lit}`xs` is at most {lit}`upper`. -/
def AllLeUpper (xs : List Nat) (upper : Nat) : Prop :=
  ∀ x ∈ xs, x ≤ upper

/-- Every element of {lit}`xs` is strictly greater than {lit}`lower`. -/
def AllGt (lower : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, lower < x

theorem ordered_tail {x : Nat} {xs : List Nat}
    (h : Ordered (x :: xs)) : Ordered xs := by
  cases xs with
  | nil =>
      trivial
  | cons _ _ =>
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

/-- Bounds survive permutation. -/
theorem allLeUpper_of_perm {xs ys : List Nat} {upper : Nat}
    (hperm : xs.Perm ys) (hys : AllLeUpper ys upper) :
    AllLeUpper xs upper := by
  intro x hx
  exact hys x (hperm.mem_iff.mp hx)

/-- Strict lower bounds survive permutation. -/
theorem allGt_of_perm {xs ys : List Nat} {lower : Nat}
    (hperm : xs.Perm ys) (hys : AllGt lower ys) :
    AllGt lower xs := by
  intro x hx
  exact hys x (hperm.mem_iff.mp hx)

/--
If the left list is sorted and bounded by the pivot, and the right list is
sorted and strictly above the pivot, then the quicksort concatenation is sorted.
-/
theorem ordered_append_pivot {left right : List Nat} {pivot : Nat}
    (hleft : Ordered left) (hright : Ordered right)
    (hle : AllLeUpper left pivot) (hgt : AllGt pivot right) :
    Ordered (left ++ pivot :: right) := by
  induction left with
  | nil =>
      have hp_right : AllLe pivot right := by
        intro x hx
        exact Nat.le_of_lt (hgt x hx)
      simpa using ordered_cons_of_allLe hright hp_right
  | cons x xs ih =>
      have hxs : Ordered xs := ordered_tail hleft
      have hle_x : x ≤ pivot := hle x (by simp)
      have hle_xs : AllLeUpper xs pivot := by
        intro y hy
        exact hle y (by simp [hy])
      have htail : Ordered (xs ++ pivot :: right) := ih hxs hle_xs
      have hbound_tail : AllLe x (xs ++ pivot :: right) := by
        intro y hy
        simp at hy
        rcases hy with hyxs | hy_pivot | hyright
        · exact ordered_allLe_tail hleft y hyxs
        · simpa [hy_pivot] using hle_x
        · exact Nat.le_trans hle_x (Nat.le_of_lt (hgt y hyright))
      simpa using ordered_cons_of_allLe htail hbound_tail

/-! ## Partition around a pivot -/

/--
Stable partition around a pivot.  The first component contains elements
{lit}`≤ p`; the second component contains elements {lit}`> p`.
-/
def partitionAround (p : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
      let parts := partitionAround p xs
      if x ≤ p then
        (x :: parts.1, parts.2)
      else
        (parts.1, x :: parts.2)

/-- The left partition contains only elements at most the pivot. -/
theorem partitionAround_left_allLeUpper (p : Nat) (xs : List Nat) :
    AllLeUpper (partitionAround p xs).1 p := by
  induction xs with
  | nil =>
      intro x hx
      simp [partitionAround] at hx
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · intro y hy
        simp [partitionAround, hxle] at hy
        rcases hy with rfl | hy
        · exact hxle
        · exact ih y hy
      · intro y hy
        simp [partitionAround, hxle] at hy
        exact ih y hy

/-- The right partition contains only elements strictly greater than the pivot. -/
theorem partitionAround_right_allGt (p : Nat) (xs : List Nat) :
    AllGt p (partitionAround p xs).2 := by
  induction xs with
  | nil =>
      intro x hx
      simp [partitionAround] at hx
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · intro y hy
        simp [partitionAround, hxle] at hy
        exact ih y hy
      · have hpx : p < x := Nat.lt_of_not_ge hxle
        intro y hy
        simp [partitionAround, hxle] at hy
        rcases hy with rfl | hy
        · exact hpx
        · exact ih y hy

/-- The left partition is no longer than the input tail. -/
theorem partitionAround_left_length_le (p : Nat) (xs : List Nat) :
    (partitionAround p xs).1.length ≤ xs.length := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · simp [partitionAround, hxle]
        exact ih
      · simp [partitionAround, hxle]
        exact Nat.le_trans ih (Nat.le_succ xs.length)

/-- The right partition is no longer than the input tail. -/
theorem partitionAround_right_length_le (p : Nat) (xs : List Nat) :
    (partitionAround p xs).2.length ≤ xs.length := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · simp [partitionAround, hxle]
        exact Nat.le_trans ih (Nat.le_succ xs.length)
      · simp [partitionAround, hxle]
        exact ih

/-- Moving an element from the middle of an append to the front preserves elements. -/
theorem perm_append_cons (x : Nat) (left right : List Nat) :
    (left ++ x :: right).Perm (x :: left ++ right) := by
  induction left with
  | nil =>
      simp
  | cons y ys ih =>
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y (ys ++ right))

/-- Partition returns exactly the input elements, just split by the pivot test. -/
theorem partitionAround_perm (p : Nat) (xs : List Nat) :
    ((partitionAround p xs).1 ++ (partitionAround p xs).2).Perm xs := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · simpa [partitionAround, hxle] using List.Perm.cons x ih
      · have hmiddle :
            ((partitionAround p xs).1 ++ x :: (partitionAround p xs).2).Perm
              (x :: (partitionAround p xs).1 ++ (partitionAround p xs).2) :=
          perm_append_cons x (partitionAround p xs).1 (partitionAround p xs).2
        exact by
          simpa [partitionAround, hxle] using hmiddle.trans (List.Perm.cons x ih)

/-! ## Functional quicksort -/

/--
Fuelled functional quicksort.  With fuel at least {lit}`xs.length`, the
recursive calls have enough fuel for the partition tails.  The public
{lit}`quickSort` below uses exactly that amount of fuel.
-/
def quickSortFuel : Nat → List Nat → List Nat
  | 0, xs => xs
  | _ + 1, [] => []
  | fuel + 1, pivot :: xs =>
      let parts := partitionAround pivot xs
      quickSortFuel fuel parts.1 ++ pivot :: quickSortFuel fuel parts.2

/-- Functional quicksort over lists of natural numbers. -/
def quickSort (xs : List Nat) : List Nat :=
  quickSortFuel xs.length xs

/-- With enough fuel, quicksort preserves the input elements up to permutation. -/
theorem quickSortFuel_perm :
    ∀ (fuel : Nat) (xs : List Nat), xs.length ≤ fuel →
      (quickSortFuel fuel xs).Perm xs := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      simp [quickSortFuel, hnil]
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil =>
          simp [quickSortFuel]
      | cons pivot tail =>
          let parts := partitionAround pivot tail
          have htail_len : tail.length ≤ fuel := by
            exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
          have hleft_len : parts.1.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_left_length_le pivot tail) htail_len
          have hright_len : parts.2.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_right_length_le pivot tail) htail_len
          have hleft_perm : (quickSortFuel fuel parts.1).Perm parts.1 :=
            ih parts.1 hleft_len
          have hright_perm : (quickSortFuel fuel parts.2).Perm parts.2 :=
            ih parts.2 hright_len
          have hboth :
              (quickSortFuel fuel parts.1 ++ pivot :: quickSortFuel fuel parts.2).Perm
                (parts.1 ++ pivot :: parts.2) :=
            List.Perm.append hleft_perm (List.Perm.cons pivot hright_perm)
          have hmiddle : (parts.1 ++ pivot :: parts.2).Perm
              (pivot :: parts.1 ++ parts.2) :=
            perm_append_cons pivot parts.1 parts.2
          have hpartition : (parts.1 ++ parts.2).Perm tail := by
            simpa [parts] using partitionAround_perm pivot tail
          simpa [quickSortFuel, parts] using
            hboth.trans (hmiddle.trans (List.Perm.cons pivot hpartition))

/-- With enough fuel, quicksort returns an ordered list. -/
theorem quickSortFuel_ordered :
    ∀ (fuel : Nat) (xs : List Nat), xs.length ≤ fuel →
      Ordered (quickSortFuel fuel xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      simp [quickSortFuel, hnil, Ordered]
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil =>
          simp [quickSortFuel, Ordered]
      | cons pivot tail =>
          let parts := partitionAround pivot tail
          have htail_len : tail.length ≤ fuel := by
            exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
          have hleft_len : parts.1.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_left_length_le pivot tail) htail_len
          have hright_len : parts.2.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_right_length_le pivot tail) htail_len
          have hleft_ordered : Ordered (quickSortFuel fuel parts.1) :=
            ih parts.1 hleft_len
          have hright_ordered : Ordered (quickSortFuel fuel parts.2) :=
            ih parts.2 hright_len
          have hleft_perm : (quickSortFuel fuel parts.1).Perm parts.1 :=
            quickSortFuel_perm fuel parts.1 hleft_len
          have hright_perm : (quickSortFuel fuel parts.2).Perm parts.2 :=
            quickSortFuel_perm fuel parts.2 hright_len
          have hleft_bound : AllLeUpper (quickSortFuel fuel parts.1) pivot :=
            allLeUpper_of_perm hleft_perm
              (by simpa [parts] using partitionAround_left_allLeUpper pivot tail)
          have hright_bound : AllGt pivot (quickSortFuel fuel parts.2) :=
            allGt_of_perm hright_perm
              (by simpa [parts] using partitionAround_right_allGt pivot tail)
          simpa [quickSortFuel, parts] using
            ordered_append_pivot hleft_ordered hright_ordered hleft_bound hright_bound

/-- Quicksort preserves the input elements up to permutation. -/
theorem quickSort_perm (xs : List Nat) :
    (quickSort xs).Perm xs := by
  exact quickSortFuel_perm xs.length xs (Nat.le_refl xs.length)

/-- Quicksort returns an ordered list. -/
theorem quickSort_ordered (xs : List Nat) :
    Ordered (quickSort xs) := by
  exact quickSortFuel_ordered xs.length xs (Nat.le_refl xs.length)

/-- The reader-facing correctness theorem for the functional quicksort model. -/
theorem quickSort_correct (xs : List Nat) :
    Ordered (quickSort xs) ∧ (quickSort xs).Perm xs :=
  ⟨quickSort_ordered xs, quickSort_perm xs⟩

end Chapter07
end CLRS
