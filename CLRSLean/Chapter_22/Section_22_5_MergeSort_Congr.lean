import Mathlib

/-!
MergeSort congruence lemma: if two comparisons agree on all pairs
from a list, mergeSort produces the same output with either.

Remaining work: `mergeSort_congr` is admitted.  See module doc for details.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V]

/-- If two comparisons agree on all elements of `l₁` cross `l₂`, then
`merge l₁ l₂` produces the same result with either comparison. -/
lemma merge_congr (le₁ le₂ : V → V → Bool) (l₁ l₂ : List V)
    (h : ∀ a ∈ l₁, ∀ b ∈ l₂, le₁ a b = le₂ a b) :
    List.merge l₁ l₂ le₁ = List.merge l₁ l₂ le₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp [List.merge]
  | cons a as ih =>
    induction l₂ with
    | nil => simp [List.merge]
    | cons b bs ih' =>
      simp [List.merge]
      rw [h a (by simp) b (by simp)]
      split
      · rw [ih (b :: bs) (fun x hx y hy =>
          h x (List.mem_cons_of_mem a hx) y hy)]
      · rw [ih' (fun x hx y hy =>
          h x hx y (List.mem_cons_of_mem b hy))]

/-- If two comparison functions `le₁` and `le₂` agree on all pairs of elements
in a list `l`, then `l.mergeSort le₁ = l.mergeSort le₂`.

**Admitted** — requires `splitAt_fst_cons` lemma (see module doc).
-/
lemma mergeSort_congr (le₁ le₂ : V → V → Bool) (l : List V)
    (h : ∀ a ∈ l, ∀ b ∈ l, le₁ a b = le₂ a b) :
    l.mergeSort le₁ = l.mergeSort le₂ := by
  sorry

end Graph
end Chapter22
end CLRS
