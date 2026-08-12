import Mathlib

/-!
# Chapter 34 — NP-Completeness Foundations (CLRS §34.1-34.3)

Lightweight formalization: P, NP, polynomial-time reducibility, NP-hardness,
NP-completeness. Complexity bounds are deferred (polyTime := True placeholder).

Status: definitions and theorem statements complete; complexity proofs deferred.
-/

namespace CLRS
namespace Chapter34

abbrev DecisionProblem (α : Type) := α → Bool

def polyTime {α β : Sort _} (_f : α → β) : Prop := True

def ClassP {α : Type} (L : DecisionProblem α) : Prop :=
  ∃ (decider : α → Bool), polyTime decider ∧ (∀ x, decider x = L x)

def ClassNP {α : Type} (L : DecisionProblem α) : Prop :=
  ∃ (β : Type) (V : α → β → Bool), polyTime V ∧ (∀ x, L x ↔ ∃ (c : β), V x c)

def polyReducesTo {α β : Type} (A : DecisionProblem α) (B : DecisionProblem β) : Prop :=
  ∃ (f : α → β), polyTime f ∧ (∀ x, A x = B (f x))

infix:50 " ≤_P " => polyReducesTo

def NP_hard {β : Type} (B : DecisionProblem β) : Prop :=
  ∀ (α : Type) (A : DecisionProblem α), ClassNP A → A ≤_P B

def NP_complete {β : Type} (B : DecisionProblem β) : Prop :=
  ClassNP B ∧ NP_hard B

theorem P_subset_NP {α : Type} (L : DecisionProblem α) (hP : ClassP L) : ClassNP L := by
  rcases hP with ⟨dec, _, hcorrect⟩
  refine ⟨Unit, (λ x _ => dec x), trivial, λ x => ?_⟩
  simp [hcorrect]

theorem polyReducesTo_trans {α β γ : Type}
    (A : DecisionProblem α) (B : DecisionProblem β) (C : DecisionProblem γ)
    (hAB : A ≤_P B) (hBC : B ≤_P C) : A ≤_P C := by
  rcases hAB with ⟨f, _, hf⟩
  rcases hBC with ⟨g, _, hg⟩
  refine ⟨g ∘ f, trivial, λ x => ?_⟩
  simp [hf x, hg (f x)]

theorem NP_complete_polyTime_implies_P_eq_NP {β : Type} (B : DecisionProblem β)
    (hNPC : NP_complete B) (hBP : ClassP B) {α : Type} (L : DecisionProblem α) :
    ClassNP L ↔ ClassP L := by
  rcases hNPC with ⟨_, hBhard⟩
  constructor
  · intro hLNP
    have h_reduce : L ≤_P B := hBhard α L hLNP
    rcases h_reduce with ⟨f, _, hf⟩
    rcases hBP with ⟨decB, _, hdecB⟩
    refine ⟨decB ∘ f, trivial, λ x => ?_⟩
    simp [hf x, hdecB (f x)]
  · exact P_subset_NP L

end Chapter34
end CLRS
