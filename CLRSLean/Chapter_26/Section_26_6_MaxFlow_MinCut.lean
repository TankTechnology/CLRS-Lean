import Mathlib
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.Ford_Fulkerson_Augmentation

/-!
# Theorem 26.6. Max-Flow Min-Cut Theorem

This file proves the complete Max-Flow Min-Cut equivalence (CLRS Theorem 26.6).
For a feasible flow, the following conditions are equivalent:

- the flow is maximal;
- the residual network has no source-to-sink augmenting path;
- some source-to-sink cut has capacity equal to the flow value.

Main results:

- `Flow.eq_cutCapacity_implies_maximal`: equality with one cut capacity
  certifies maximality.
- `Flow.maximal_iff_noAugmentingPath`: maximality is equivalent to the absence
  of an augmenting path.
- `Flow.maximal_iff_exists_cut_value_eq`: maximality is equivalent to the
  existence of a cut whose capacity equals the flow value.

**Current gaps**: none for the mathematical Max-Flow Min-Cut equivalence.
Executable Ford--Fulkerson and Edmonds--Karp algorithms are developed
separately.
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
  · subst hl; simp
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

/-- A feasible flow is maximal exactly when its residual network contains no
source-to-sink augmenting path. -/
theorem Flow.maximal_iff_noAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) :
    φ.isMaximal ↔ ¬φ.hasAugmentingPath := by
  constructor
  · intro hmax hpath
    exact φ.not_maximal_of_hasAugmentingPath hpath hmax
  · exact φ.maximal_of_noAugmentingPath

/-- **Max-Flow Min-Cut Theorem (CLRS Theorem 26.6).** A feasible flow is
maximal exactly when some cut separating source and sink has capacity equal to
the flow value. -/
theorem Flow.maximal_iff_exists_cut_value_eq {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} (φ : Flow V G) :
    φ.isMaximal ↔
      ∃ S : Finset V, G.s ∈ S ∧ G.t ∉ S ∧
        φ.value = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
  constructor
  · intro hmax
    exact φ.exists_cut_value_eq_of_noAugmentingPath
      ((φ.maximal_iff_noAugmentingPath).mp hmax)
  · rintro ⟨S, hs, ht, hvalue⟩
    exact φ.eq_cutCapacity_implies_maximal S hs ht hvalue

end Chapter26
end CLRS
