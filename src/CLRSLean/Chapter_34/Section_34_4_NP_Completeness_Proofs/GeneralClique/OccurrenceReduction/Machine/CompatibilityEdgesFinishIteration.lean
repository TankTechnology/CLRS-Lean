import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitRows
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: finish one outer iteration

After every prior row has been emitted, the controller reverses the temporary
row stack back onto work one, clears the current upper endpoint, and returns
to the outer-loop entry.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private def compatibilityEdges_restoreRowsRun
    (symbols input work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .restoreRows buffer₁ buffer₂ test input output
        work₁ symbols upper 0 0)
      (some (compatibilityEdgesCfg .clearCurrentVertex buffer₁ none test input
        output (symbols.reverse ++ work₁) [] upper 0 0))
      (symbols.length + 1) := by
  induction symbols generalizing buffer₂ work₁ with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | cons symbol symbols ih =>
      let after := compatibilityEdgesCfg .restoreRows buffer₁ (some symbol)
        test input output (symbol :: work₁) symbols upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .restoreRows buffer₁ buffer₂ test input
            output work₁ (symbol :: symbols) upper 0 0)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some symbol) (work₁ := symbol :: work₁)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (symbols.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def compatibilityEdges_clearCurrentVertexRun
    (upper : Nat) (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearCurrentVertex buffer₁ buffer₂ test input
        output work₁ work₂ upper 0 0)
      (some (compatibilityEdgesCfg .outer buffer₁ buffer₂ false input output
        work₁ work₂ 0 0 0)) (upper + 1) := by
  induction upper generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ upper ih =>
      let after := compatibilityEdgesCfg .clearCurrentVertex buffer₁ buffer₂
        true input output work₁ work₂ upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .clearCurrentVertex buffer₁ buffer₂ test
            input output work₁ work₂ (upper + 1) 0 0)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, List.replicate_succ, step,
            compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (upper + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact suffix run after the last emitted prior row. -/
def compatibilityEdgesFinishIterationSteps
    (upper : Nat) (symbols : List UnaryFrameSym) : Nat :=
  symbols.length + upper + 3

/-- An empty emission source triggers row restoration and returns to a clean
outer-loop entry with the reversed temporary stack on work one. -/
def compatibilityEdges_finishIterationRun
    (upper : Nat) (symbols input : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .emitStart buffer₁ buffer₂ test input output
        [] symbols upper 0 0)
      (some (compatibilityEdgesCfg .outer none none false input output
        symbols.reverse [] 0 0 0))
      (compatibilityEdgesFinishIterationSteps upper symbols) := by
  have boundary : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .emitStart buffer₁ buffer₂ test input output
        [] symbols upper 0 0)
      (some (compatibilityEdgesCfg .restoreRows none buffer₂ test input output
        [] symbols upper 0 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  have restore := compatibilityEdges_restoreRowsRun symbols input [] output
    none buffer₂ test upper
  have clear := compatibilityEdges_clearCurrentVertexRun upper input
    symbols.reverse [] output none none test
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    1 (symbols.length + 1) _ _ _ boundary restore
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (upper + 1) _ _ _ first (by simpa using clear)
  simpa [compatibilityEdgesFinishIterationSteps, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
