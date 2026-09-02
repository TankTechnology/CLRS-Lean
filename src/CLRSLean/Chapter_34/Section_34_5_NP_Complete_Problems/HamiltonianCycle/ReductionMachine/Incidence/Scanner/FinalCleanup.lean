import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Iteration

/-!
# HAM-CYCLE incidence scanner: final cleanup
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder

/-- Discard the restored graph and traverse the already-empty scratch tapes. -/
def discardGraph_run (input : List (Option CliqueSym))
    (output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .discardGraph buffer₁ buffer₂ test input output [] [] [] [] [])
      (some (haltCfg program output))
      (input.length + 7) := by
  induction input generalizing buffer₁ with
  | nil =>
      exact ⟨⟨7, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg, stepOp,
          haltCfg]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg .discardGraph (some symbol) buffer₂ test input output
        [] [] [] [] []
      have first : EvalsToInTime (step program)
          (cfg .discardGraph buffer₁ buffer₂ test (symbol :: input)
            output [] [] [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 7) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Empty query work means every incidence row has been generated. -/
def final_run (input : List (Option CliqueSym))
    (output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test input output [] [] [] [] [])
      (some (haltCfg program output))
      (input.length + 8) := by
  let after := cfg .discardGraph none buffer₂ test input output [] [] [] [] []
  have first : EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test input output [] [] [] [] [])
      (some after) 1 :=
    ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
  have rest := discardGraph_run input output none buffer₂ test
  let full := EvalsToInTime.trans (step program)
    1 (input.length + 7) _ after _ first rest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- The canonical query stream carries one leading certificate marker.  It
is the terminal stack symbol after every reversed vertex record is consumed. -/
def terminal_run (input : List (Option CliqueSym))
    (output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test input output
        [some CliqueSym.certificateMark] [] [] [] [])
      (some (haltCfg program output))
      (input.length + 8) := by
  let after := cfg .discardGraph (some (some CliqueSym.certificateMark))
    buffer₂ test input output [] [] [] [] []
  have first : EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test input output
        [some CliqueSym.certificateMark] [] [] [] [])
      (some after) 1 :=
    ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
  have rest := discardGraph_run input output
    (some (some CliqueSym.certificateMark)) buffer₂ test
  let full := EvalsToInTime.trans (step program)
    1 (input.length + 7) _ after _ first rest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner
