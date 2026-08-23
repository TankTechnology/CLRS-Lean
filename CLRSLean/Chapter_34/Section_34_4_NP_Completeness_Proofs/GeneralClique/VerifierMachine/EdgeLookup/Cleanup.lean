import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Canonical
import Mathlib.Tactic

/-!
# General CLIQUE verifier: edge-lookup cleanup
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

def clear₃_run (answer : Bool) (scratch : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clear₃ answer) buffer₁ buffer₂ test [] [] [] []
        (List.replicate scratch ()))
      (some (haltCfg program [answer])) (scratch + 3) := by
  induction scratch generalizing test with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ scratch ih =>
      let after := cfg (.clear₃ answer) buffer₁ buffer₂ true [] [] [] []
        (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clear₃ answer) buffer₁ buffer₂ test [] [] [] []
            (List.replicate (scratch + 1) ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (scratch + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clear₂_run (answer : Bool) (right scratch : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clear₂ answer) buffer₁ buffer₂ test [] [] []
        (List.replicate right ()) (List.replicate scratch ()))
      (some (haltCfg program [answer])) (right + scratch + 4) := by
  induction right generalizing test with
  | zero =>
      let after := cfg (.clear₃ answer) buffer₁ buffer₂ false [] [] [] []
        (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clear₂ answer) buffer₁ buffer₂ test [] [] [] []
            (List.replicate scratch ())) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clear₃_run answer scratch buffer₁ buffer₂ false
      let full := EvalsToInTime.trans (step program)
        1 (scratch + 3) _ after _ first rest
      simpa using full
  | succ right ih =>
      let after := cfg (.clear₂ answer) buffer₁ buffer₂ true [] [] []
        (List.replicate right ()) (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clear₂ answer) buffer₁ buffer₂ test [] [] []
            (List.replicate (right + 1) ()) (List.replicate scratch ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (right + scratch + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clear₁_run (answer : Bool) (left right scratch : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clear₁ answer) buffer₁ buffer₂ test [] []
        (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ()))
      (some (haltCfg program [answer])) (left + right + scratch + 5) := by
  induction left generalizing test with
  | zero =>
      let after := cfg (.clear₂ answer) buffer₁ buffer₂ false [] [] []
        (List.replicate right ()) (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clear₁ answer) buffer₁ buffer₂ test [] [] []
            (List.replicate right ()) (List.replicate scratch ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clear₂_run answer right scratch buffer₁ buffer₂ false
      let full := EvalsToInTime.trans (step program)
        1 (right + scratch + 4) _ after _ first rest
      simpa using full
  | succ left ih =>
      let after := cfg (.clear₁ answer) buffer₁ buffer₂ true [] []
        (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clear₁ answer) buffer₁ buffer₂ test [] []
            (List.replicate (left + 1) ()) (List.replicate right ())
            (List.replicate scratch ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (left + right + scratch + 5) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearInput_run (answer : Bool) (input : List (Option CliqueSym))
    (left right scratch : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput answer) buffer₁ buffer₂ test input []
        (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ()))
      (some (haltCfg program [answer]))
      (input.length + left + right + scratch + 6) := by
  induction input generalizing buffer₁ with
  | nil =>
      let after := cfg (.clear₁ answer) none buffer₂ test [] []
        (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer₁ buffer₂ test [] []
            (List.replicate left ()) (List.replicate right ())
            (List.replicate scratch ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clear₁_run answer left right scratch none buffer₂ test
      let full := EvalsToInTime.trans (step program)
        1 (left + right + scratch + 5) _ after _ first rest
      simpa using full
  | cons symbol input ih =>
      let after := cfg (.clearInput answer) (some symbol) buffer₂ test input []
        (List.replicate left ()) (List.replicate right ())
        (List.replicate scratch ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer₁ buffer₂ test (symbol :: input) []
            (List.replicate left ()) (List.replicate right ())
            (List.replicate scratch ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + left + right + scratch + 6)
        _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
