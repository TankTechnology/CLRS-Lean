import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Basic
import Mathlib.Tactic

/-!
# General CLIQUE verifier: endpoint-bound cleanup and restoration
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

open PolyBuilder

def emit_run (answer : Bool) (buffer₁ buffer₂ : Option (Option CliqueSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emit answer) buffer₁ buffer₂ test [] [] [] [])
      (some (haltCfg program [answer])) 2 := by
  exact ⟨⟨2, by
    simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩

def clearWork₂_run (answer : Bool) (work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearWork₂ answer) buffer₁ buffer₂ test [] [] [] work₂)
      (some (haltCfg program [answer])) (work₂.length + 3) := by
  induction work₂ generalizing buffer₂ with
  | nil =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | cons symbol work₂ ih =>
      let after := cfg (.clearWork₂ answer) buffer₁ (some symbol)
        test [] [] [] work₂
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₂ answer) buffer₁ buffer₂ test [] [] []
            (symbol :: work₂)) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₂.length + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearWork₁_run (answer : Bool) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearWork₁ answer) buffer₁ buffer₂ test [] [] work₁ work₂)
      (some (haltCfg program [answer]))
      (work₁.length + work₂.length + 4) := by
  induction work₁ generalizing buffer₁ with
  | nil =>
      let after := cfg (.clearWork₂ answer) none buffer₂ test
        [] [] [] work₂
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₁ answer) buffer₁ buffer₂ test
            [] [] [] work₂) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearWork₂_run answer work₂ none buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (work₂.length + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol work₁ ih =>
      let after := cfg (.clearWork₁ answer) (some symbol) buffer₂ test
        [] [] work₁ work₂
      have first : EvalsToInTime (step program)
          (cfg (.clearWork₁ answer) buffer₁ buffer₂ test [] []
            (symbol :: work₁) work₂) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (work₁.length + work₂.length + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearInput_run (answer : Bool) (input work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput answer) buffer₁ buffer₂ test input [] work₁ work₂)
      (some (haltCfg program [answer]))
      (input.length + work₁.length + work₂.length + 5) := by
  induction input generalizing buffer₁ with
  | nil =>
      let after := cfg (.clearWork₁ answer) none buffer₂ test
        [] [] work₁ work₂
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer₁ buffer₂ test
            [] [] work₁ work₂) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearWork₁_run answer work₁ work₂
        none buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (work₁.length + work₂.length + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol input ih =>
      let after := cfg (.clearInput answer) (some symbol) buffer₂ test
        input [] work₁ work₂
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer₁ buffer₂ test
            (symbol :: input) [] work₁ work₂) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + work₁.length + work₂.length + 5)
        _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Restore the consumed unary budget from work stack two to work stack one. -/
def restore_run (remaining spent : Nat) (input : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .restore buffer₁ buffer₂ test input []
        (List.replicate remaining (some .tick))
        (List.replicate spent (some .tick)))
      (some (cfg .edges buffer₁ none test input []
        (List.replicate (remaining + spent) (some .tick)) []))
      (spent + 1) := by
  induction spent generalizing remaining buffer₂ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ spent ih =>
      let after := cfg .restore buffer₁ (some (some .tick)) test input []
        (some .tick :: List.replicate remaining (some .tick))
        (List.replicate spent (some .tick))
      have first : EvalsToInTime (step program)
          (cfg .restore buffer₁ buffer₂ test input []
            (List.replicate remaining (some .tick))
            (List.replicate (spent + 1) (some .tick)))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (remaining := remaining + 1)
        (buffer₂ := some (some .tick))
      let full := EvalsToInTime.trans (step program)
        1 (spent + 1) _ after _ first rest
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound
