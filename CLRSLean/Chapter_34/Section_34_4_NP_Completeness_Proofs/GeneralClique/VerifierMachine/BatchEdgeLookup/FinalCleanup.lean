import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Query

/-!
# Batch edge lookup: final cleanup
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Discard the restored graph and traverse the empty cleanup stacks. -/
def discardGraph_run (answer : Bool) (input : List (Option CliqueSym))
    (output : List Bool)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.discardGraph answer) buffer₁ buffer₂ test input output [] [] [] [] [])
      (some (haltCfg program (answer :: output)))
      (input.length + 8) := by
  induction input generalizing buffer₁ with
  | nil =>
      exact ⟨⟨8, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg, stepOp,
          haltCfg]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg (.discardGraph answer) (some symbol) buffer₂ test input
        output [] [] [] [] []
      have first : EvalsToInTime (step program)
          (cfg (.discardGraph answer) buffer₁ buffer₂ test (symbol :: input)
            output [] [] [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 8) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Empty query work means the aggregate is final. -/
def final_run (answer : Bool) (input : List (Option CliqueSym))
    (output : List Bool)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextQuery answer) buffer₁ buffer₂ test input output [] [] [] [] [])
      (some (haltCfg program (answer :: output)))
      (input.length + 9) := by
  let after := cfg (.discardGraph answer) none buffer₂ test input output [] [] [] [] []
  have first : EvalsToInTime (step program)
      (cfg (.nextQuery answer) buffer₁ buffer₂ test input output [] [] [] [] [])
      (some after) 1 :=
    ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
  have rest := discardGraph_run answer input output none buffer₂ test
  let full := EvalsToInTime.trans (step program)
    1 (input.length + 8) _ after _ first rest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup
