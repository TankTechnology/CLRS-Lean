import Mathlib
import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

/-!
# 26.1. Max-Flow Min-Cut Theorem (partial)

This file proves part of the Max-Flow Min-Cut Theorem (CLRS Theorem 26.6).

**Proved**:
* `eq_cutCapacity_implies_maximal`: if `|f| = c(S,T)` for some cut `(S,T)` with `s ∈ S`, `t ∉ S`,
  then `f` is maximal (the easy direction, using `value_le_cut_capacity`).

**Missing**:
* The forward direction of the equivalence: `maximal ⇒ ∃ cut with |f| = c(S,T)`.
  This requires constructing the cut from the residual-network reachability set and proving
  `|f| = c(S,Sᶜ)` when `f` is maximal. The construction is already written in
  `maximal_of_noAugmentingPath` for the case `¬hasAugmentingPath`; the converse
  `maximal ⇒ ¬hasAugmentingPath` requires the constructive augmentation lemma
  (`hasAugmentingPath ⇒ ¬isMaximal`) which is deferred to a follow-up formalization.

* The three-condition equivalence `maximal ↔ no augmenting path ↔ |f| = c(S,T)` is not yet
  proved as a single chain.  The forward implication `no augmenting path ⇒ maximal` is already
  proved in `Section_26_1_Flow_Networks` as `Flow.maximal_of_noAugmentingPath`.

**Status**: partial.
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset Classical

/-- Every consecutive pair from a `List.IsChain` chain satisfies the relation. -/
lemma forall_zip_edges_of_isChain {V : Type*} {r : V → V → Prop} {a : V} {l : List V}
    (h : List.IsChain r (a :: l)) : ∀ (u v : V), (u, v) ∈ List.zip (a :: l) l → r u v := by
  have h_eq : l = [] ∨ ∃ (b : V) (l' : List V), l = b :: l' := by
    cases l
    · left; rfl
    · right; refine ⟨_, _, rfl⟩
  rcases h_eq with (hl | ⟨b, l', hl⟩)
  · subst hl; cases h <;> simp
  · subst hl
    have h_cons_cons := (List.isChain_cons_cons (a := a) (b := b) (l := l')).mp h
    rcases h_cons_cons with ⟨h_rel, h_chain⟩
    intro u v h_mem
    have h_zip : List.zip (a :: b :: l') (b :: l') = (a, b) :: List.zip (b :: l') l' := by simp
    simp [h_zip] at h_mem
    rcases h_mem with (⟨rfl, rfl⟩ | h_rest)
    · exact h_rel
    · exact forall_zip_edges_of_isChain h_chain u v h_rest

/-- If the value of a flow equals the capacity of some cut, the flow is maximal.
    This is the easy direction of Theorem 26.6. -/
theorem Flow.eq_cutCapacity_implies_maximal {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (S : Finset V) (hs : G.s ∈ S) (ht : G.t ∉ S)
    (h_eq : φ.value = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v))) :
    Flow.isMaximal φ := by
  intro ψ
  have hψ_le : ψ.value ≤ Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) :=
    Flow.value_le_cut_capacity φ ψ S hs ht
  linarith

end Chapter26
end CLRS
