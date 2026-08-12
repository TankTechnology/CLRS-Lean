import Mathlib

/-!
MergeSort congruence lemma: if two comparisons agree on all pairs
from a list, mergeSort produces the same output with either.

The main lemma is {lit}`mergeSort_congr`.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type}

private lemma splitInTwo_fst_subset {α : Type} {n : Nat} (l : {l : List α // l.length = n}) :
    ((List.MergeSort.Internal.splitInTwo l).1 : List α) ⊆ (l : List α) := by
  intro x hx
  simp [List.MergeSort.Internal.splitInTwo, List.splitAt_eq] at hx ⊢
  exact List.mem_of_mem_take hx

private lemma splitInTwo_snd_subset {α : Type} {n : Nat} (l : {l : List α // l.length = n}) :
    ((List.MergeSort.Internal.splitInTwo l).2 : List α) ⊆ (l : List α) := by
  intro x hx
  simp [List.MergeSort.Internal.splitInTwo, List.splitAt_eq] at hx ⊢
  exact List.mem_of_mem_drop hx

/-- If two comparisons agree on all elements of {lit}`l₁` cross {lit}`l₂`,
then {lit}`merge l₁ l₂` produces the same result with either comparison. -/
lemma merge_congr (le₁ le₂ : V → V → Bool) (l₁ l₂ : List V)
    (h : ∀ a ∈ l₁, ∀ b ∈ l₂, le₁ a b = le₂ a b) :
    List.merge l₁ l₂ le₁ = List.merge l₁ l₂ le₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a as ih =>
    induction l₂ with
    | nil => simp
    | cons b bs ih' =>
      simp [List.merge]
      rw [h a (by simp) b (by simp)]
      split
      · rw [ih (b :: bs) (fun x hx y hy =>
          h x (List.mem_cons_of_mem a hx) y hy)]
      · rw [ih' (fun x hx y hy =>
          h x hx y (List.mem_cons_of_mem b hy))]

/-- If two comparison functions {lit}`le₁` and {lit}`le₂` agree on all pairs of
elements in a list {lit}`l`, then {lit}`l.mergeSort le₁ = l.mergeSort le₂`.
-/
lemma mergeSort_congr (le₁ le₂ : V → V → Bool) (l : List V)
    (h : ∀ a ∈ l, ∀ b ∈ l, le₁ a b = le₂ a b) :
    l.mergeSort le₁ = l.mergeSort le₂ := by
  rw [List.mergeSort.eq_def, List.mergeSort.eq_def]
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: xs =>
      let l' : {l : List V // l.length = (a :: b :: xs).length} := ⟨a :: b :: xs, rfl⟩
      let lr := List.MergeSort.Internal.splitInTwo l'
      have hleft :
          ((lr.1 : List V).mergeSort le₁) = ((lr.1 : List V).mergeSort le₂) := by
        apply mergeSort_congr
        intro x hx y hy
        exact h x (splitInTwo_fst_subset l' hx) y (splitInTwo_fst_subset l' hy)
      have hright :
          ((lr.2 : List V).mergeSort le₁) = ((lr.2 : List V).mergeSort le₂) := by
        apply mergeSort_congr
        intro x hx y hy
        exact h x (splitInTwo_snd_subset l' hx) y (splitInTwo_snd_subset l' hy)
      have hcross : ∀ x ∈ (lr.1 : List V).mergeSort le₂,
          ∀ y ∈ (lr.2 : List V).mergeSort le₂, le₁ x y = le₂ x y := by
        intro x hx y hy
        have hx' : x ∈ (lr.1 : List V) := (List.mergeSort_perm (lr.1 : List V) le₂).mem_iff.mp hx
        have hy' : y ∈ (lr.2 : List V) := (List.mergeSort_perm (lr.2 : List V) le₂).mem_iff.mp hy
        exact h x (splitInTwo_fst_subset l' hx') y (splitInTwo_snd_subset l' hy')
      change
        ((lr.1 : List V).mergeSort le₁).merge ((lr.2 : List V).mergeSort le₁) le₁ =
          ((lr.1 : List V).mergeSort le₂).merge ((lr.2 : List V).mergeSort le₂) le₂
      rw [hleft, hright]
      exact merge_congr le₁ le₂ ((lr.1 : List V).mergeSort le₂)
        ((lr.2 : List V).mergeSort le₂) hcross
termination_by l.length
decreasing_by
  simp_wf
  all_goals
    try simp [List.MergeSort.Internal.splitInTwo, List.splitAt_eq]
    omega

end Graph
end Chapter22
end CLRS
