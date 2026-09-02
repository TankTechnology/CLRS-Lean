import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Basic
import Mathlib.Tactic

/-!
# General CLIQUE verifier: normalized-edge cleanup phases
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

open PolyBuilder

def emit_run (answer : Bool) (buffer : Option (Option CliqueSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emit answer) buffer test [] [] [])
      (some (haltCfg program [answer])) 2 := by
  exact ⟨⟨2, by
    simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩

def clearCount_run (answer : Bool) (count : Nat)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearCount answer) buffer test [] []
        (List.replicate count ()))
      (some (haltCfg program [answer])) (count + 3) := by
  induction count generalizing test with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := cfg (.clearCount answer) buffer true [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearCount answer) buffer test [] []
            (List.replicate (count + 1) ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def clearInput_run (answer : Bool) (input : List (Option CliqueSym))
    (count : Nat) (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.clearInput answer) buffer test input []
        (List.replicate count ()))
      (some (haltCfg program [answer])) (input.length + count + 4) := by
  induction input generalizing buffer test with
  | nil =>
      let after := cfg (.clearCount answer) none test [] []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer test [] []
            (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clearCount_run answer count none test
      let full := EvalsToInTime.trans (step program)
        1 (count + 3) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons symbol input ih =>
      let after := cfg (.clearInput answer) (some symbol) test input []
        (List.replicate count ())
      have first : EvalsToInTime (step program)
          (cfg (.clearInput answer) buffer test (symbol :: input) []
            (List.replicate count ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer := some symbol) (test := test)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + count + 4) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder
