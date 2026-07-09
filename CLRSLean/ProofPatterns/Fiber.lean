import Mathlib

/-!
# Fiber decomposition proof pattern

This module contains the generic list lemmas behind bucket-style proofs: group
elements by a key, prove facts fiber-by-fiber, then concatenate or scan the
fibers in key order.

Counting sort, radix sort, bucket sort, and hash-table chain arguments are the
main local examples of this shape.
-/

namespace CLRS
namespace ProofPatterns

/--
The fiber of a list at key {lit}`k`, preserving the source-list order.

This is the key-generic version of the counting-sort {lit}`bucket` helper.
-/
def fiber [DecidableEq κ] (key : α -> κ) (xs : List α) (k : κ) : List α :=
  xs.filter fun x => key x = k

theorem fiber_sublist [DecidableEq κ] (key : α -> κ) (xs : List α) (k : κ) :
    (fiber key xs k).Sublist xs := by
  unfold fiber
  exact List.filter_sublist

theorem fiber_append [DecidableEq κ] (key : α -> κ) (xs ys : List α) (k : κ) :
    fiber key (xs ++ ys) k = fiber key xs k ++ fiber key ys k := by
  simp [fiber]

theorem mem_fiber_iff [DecidableEq κ] {key : α -> κ} {xs : List α} {k : κ} {x : α} :
    x ∈ fiber key xs k <-> x ∈ xs ∧ key x = k := by
  simp [fiber]

theorem fiber_all_keys_eq [DecidableEq κ] (key : α -> κ) (xs : List α) (k : κ) :
    forall x, x ∈ fiber key xs k -> key x = k := by
  intro x hx
  exact (mem_fiber_iff.mp hx).2

theorem fiber_eq_nil_of_forall_ne [DecidableEq κ]
    {key : α -> κ} {xs : List α} {k : κ}
    (h : forall x, x ∈ xs -> key x ≠ k) :
    fiber key xs k = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  exact h x (mem_fiber_iff.mp hx).1 (mem_fiber_iff.mp hx).2

/--
Filtering a fiber by another key keeps it exactly when both keys are the same;
otherwise the second fiber is empty.
-/
theorem fiber_fiber_eq [DecidableEq κ]
    (key : α -> κ) (xs : List α) (j k : κ) :
    fiber key (fiber key xs j) k = if j = k then fiber key xs k else [] := by
  by_cases hjk : j = k
  · subst j
    simp [fiber, List.filter_filter]
  · simp [hjk]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hxj : key x = j := (mem_fiber_iff.mp (mem_fiber_iff.mp hx).1).2
    have hxk : key x = k := (mem_fiber_iff.mp hx).2
    have h_eq : j = k := by
      rw [<- hxj, hxk]
    exact hjk h_eq

end ProofPatterns
end CLRS
