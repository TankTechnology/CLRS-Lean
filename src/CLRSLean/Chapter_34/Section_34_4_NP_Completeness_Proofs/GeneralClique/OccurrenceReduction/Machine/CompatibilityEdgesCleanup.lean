import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesPriorRows
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: current-counter cleanup

After every prior row has been tagged, the controller clears the current
clause and variable counters before restoring the tagged row family.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private def compatibilityEdges_clearClauseRun
    (clause : Nat) (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper variableCode : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper clause variableCode)
      (some (compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 variableCode))
      (clause + 1) := by
  induction clause generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ clause ih =>
      let after := compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂
        true input output outputWork₁ work₂ upper clause variableCode
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
            input output outputWork₁ work₂ upper (clause + 1)
            variableCode) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (clause + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def compatibilityEdges_clearVariableRun
    (variableCode : Nat)
    (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper 0 variableCode)
      (some (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 0))
      (variableCode + 1) := by
  induction variableCode generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ variableCode ih =>
      let after := compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂
        true input output outputWork₁ work₂ upper 0 variableCode
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .clearCurrentVariable buffer₁ buffer₂ test
            input output outputWork₁ work₂ upper 0
            (variableCode + 1)) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (variableCode + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cleanup run from populated current-row counters to the tagged-row
restoration entry.  The upper endpoint remains available in counter one. -/
def compatibilityEdges_cleanupCurrentRun
    (upper clause variableCode : Nat)
    (input outputWork₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentClause buffer₁ buffer₂ test
        input output outputWork₁ work₂ upper clause variableCode)
      (some (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂
        false input output outputWork₁ work₂ upper 0 0))
      (clause + variableCode + 2) := by
  have first := compatibilityEdges_clearClauseRun clause input outputWork₁
    work₂ output buffer₁ buffer₂ test upper variableCode
  have rest := compatibilityEdges_clearVariableRun variableCode input
    outputWork₁ work₂ output buffer₁ buffer₂ false upper
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (clause + 1) (variableCode + 1) _ _ _ first rest
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
