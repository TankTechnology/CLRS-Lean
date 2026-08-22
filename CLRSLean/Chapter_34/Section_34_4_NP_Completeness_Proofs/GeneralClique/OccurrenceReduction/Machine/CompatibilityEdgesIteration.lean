import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesFinishIteration
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: one complete outer iteration

This file composes current-row parsing, every prior comparison, tagged
restoration, conditional edge emission, row restoration, and counter cleanup
for one current occurrence.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem encodeReversedOccurrenceEntries_reverse
    (entries : List (IndexedOccurrence × Nat)) :
    (encodeReversedOccurrenceEntries entries.reverse).reverse =
      encodeIndexedOccurrenceEntries entries := by
  induction entries with
  | nil =>
      simp [encodeReversedOccurrenceEntries, encodeIndexedOccurrenceEntries]
  | cons entry entries ih =>
      rw [List.reverse_cons]
      simp only [encodeReversedOccurrenceEntries, encodeIndexedOccurrenceEntries,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.reverse_append, List.reverse_reverse]
      simpa [encodeReversedOccurrenceEntries, encodeIndexedOccurrenceEntries]
        using ih

/-- Exact budget for one complete current-versus-priors iteration. -/
def compatibilityEdgesOuterIterationSteps
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : Nat :=
  compatibilityEdgesCurrentRowSteps current +
    compatibilityEdgesPriorRowsSteps current priors + 1 +
    (current.1.clauseIndex + occurrenceVariableCode current.1.literal + 2) +
    compatibilityEdgesRestoreTaggedRowsSteps priors.reverse +
    compatibilityEdgesEmitPriorRowsSteps current priors +
    compatibilityEdgesFinishIterationSteps current.2
      (encodeReversedOccurrenceEntries priors.reverse)

/-- One complete outer iteration removes the current row, compares it with
every remaining row, emits exactly the compatible lower-to-upper edges, and
returns with the remaining rows restored in forward physical order. -/
def compatibilityEdges_outerIterationRun
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer buffer₁ buffer₂ test [] output
        (encodeIndexedOccurrenceEntry current ++
          encodeIndexedOccurrenceEntries priors) [] 0 0 0)
      (some (compatibilityEdgesCfg .outer none none false []
        (encodeCompatibleOccurrenceEdges current priors.reverse ++ output)
        (encodeIndexedOccurrenceEntries priors) [] 0 0 0))
      (compatibilityEdgesOuterIterationSteps current priors) := by
  have currentRun := compatibilityEdges_currentRowRun current
    (encodeIndexedOccurrenceEntries priors) output buffer₁ buffer₂ test
  rcases compatibilityEdges_priorRowsRun current priors [] [] output
      (some .frameEnd) buffer₂ test with
    ⟨afterPriorBuffer₁, afterPriorBuffer₂, afterPriorTest, priorRun⟩
  have priorDone := compatibilityEdges_priorRowsDoneRun current
    (encodeTaggedOccurrenceEntries current priors.reverse) output
    afterPriorBuffer₁ afterPriorBuffer₂ afterPriorTest
  have cleanup := compatibilityEdges_cleanupCurrentRun current.2
    current.1.clauseIndex (occurrenceVariableCode current.1.literal)
    [] [] (encodeTaggedOccurrenceEntries current priors.reverse) output
    none afterPriorBuffer₂ afterPriorTest
  rcases compatibilityEdges_restoreTaggedRowsRun current priors.reverse [] []
      output none afterPriorBuffer₂ false current.2 with
    ⟨afterRestoreBuffer₂, restoreRun⟩
  rcases compatibilityEdges_emitPriorRowsRun current priors [] [] output none
      afterRestoreBuffer₂ false with
    ⟨afterEmitBuffer₁, emitRun⟩
  have finishRun := compatibilityEdges_finishIterationRun current.2
    (encodeReversedOccurrenceEntries priors.reverse) []
    (encodeCompatibleOccurrenceEdges current priors.reverse ++ output)
    afterEmitBuffer₁ afterRestoreBuffer₂ false
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (compatibilityEdgesCurrentRowSteps current)
    (compatibilityEdgesPriorRowsSteps current priors) _ _ _ currentRun (by
      simpa using priorRun)
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ first priorDone
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (current.1.clauseIndex +
      occurrenceVariableCode current.1.literal + 2) _ _ _ second cleanup
  let fourth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (compatibilityEdgesRestoreTaggedRowsSteps priors.reverse)
    _ _ _ third restoreRun
  let fifth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (compatibilityEdgesEmitPriorRowsSteps current priors) _ _ _ fourth (by
      simpa [List.reverse_reverse] using emitRun)
  have finalTest_eq :
      compatibilityEdgesEmitPriorRowsFinalTest false priors = false := by
    cases priors <;> rfl
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (compatibilityEdgesFinishIterationSteps current.2
      (encodeReversedOccurrenceEntries priors.reverse)) _ _ _ fifth (by
        simpa [finalTest_eq] using finishRun)
  convert full using 1 <;>
    simp [compatibilityEdgesOuterIterationSteps,
      encodeReversedOccurrenceEntries_reverse,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end TMClique
end Turing
end Chapter34
end CLRS
