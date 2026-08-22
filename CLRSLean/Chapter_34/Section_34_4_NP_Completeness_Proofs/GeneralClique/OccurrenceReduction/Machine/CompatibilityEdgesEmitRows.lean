import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitEdge
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: emit every prior row

This file joins compatible and incompatible row dispatch, clears the lower
counter, and iterates the complete flagged row family.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private def compatibilityEdges_clearLowerRun
    (lower : Nat) (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .clearLower buffer₁ buffer₂ test input output
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .emitStart buffer₁ buffer₂ false input
        output work₁ work₂ upper 0 0)) (lower + 1) := by
  induction lower generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ lower ih =>
      let after := compatibilityEdgesCfg .clearLower buffer₁ buffer₂ true
        input output work₁ work₂ upper lower 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .clearLower buffer₁ buffer₂ test input
            output work₁ work₂ upper (lower + 1) 0)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, List.replicate_succ, step,
            compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (lower + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Optional edge record contributed by one prior occurrence. -/
def encodeCompatibleOccurrenceEdge
    (current prior : IndexedOccurrence × Nat) : List CliqueSym :=
  if indexedOccurrencesCompatibleCode current prior then
    encodeCliqueEdge (prior.2, current.2)
  else []

/-- Exact budget for scanning, optionally emitting, and clearing one row. -/
def compatibilityEdgesEmitPriorRowSteps
    (current prior : IndexedOccurrence × Nat) : Nat :=
  compatibilityEdgesEmitFlaggedRowSteps prior +
    (if indexedOccurrencesCompatibleCode current prior then
      compatibilityEdgesEmitCompatibleEdgeSteps current.2 prior.2
    else 0) + prior.2 + 1

/-- One flagged prior row either emits its exact normalized edge or emits
nothing, then returns to the next-row entry with a clean lower counter. -/
def compatibilityEdges_emitPriorRowRun
    (current prior : IndexedOccurrence × Nat)
    (tail work₂ input : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .emitStart buffer₁ buffer₂ test input output
        (encodeFlaggedOccurrenceEntry current prior ++ tail) work₂
        current.2 0 0)
      (some (compatibilityEdgesCfg .emitStart
        (some (if indexedOccurrencesCompatibleCode current prior then
          .tick else .separator)) buffer₂ false input
        (encodeCompatibleOccurrenceEdge current prior ++ output) tail
        ((encodeIndexedOccurrenceEntry prior).reverse ++ work₂)
        current.2 0 0))
      (compatibilityEdgesEmitPriorRowSteps current prior) := by
  cases compatible : indexedOccurrencesCompatibleCode current prior with
  | false =>
      have scan := compatibilityEdges_emitFlaggedRowRun prior false tail work₂
        input output buffer₁ buffer₂ test current.2
      have clear := compatibilityEdges_clearLowerRun prior.2 input tail
        ((encodeIndexedOccurrenceEntry prior).reverse ++ work₂) output
        (some .separator) buffer₂ test current.2
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesEmitFlaggedRowSteps prior) (prior.2 + 1)
        _ _ _ (by
          simpa [encodeFlaggedOccurrenceEntry, compatible] using scan) clear
      simpa [compatible, encodeFlaggedOccurrenceEntry,
        encodeCompatibleOccurrenceEdge,
        compatibilityEdgesEmitPriorRowSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | true =>
      have scan := compatibilityEdges_emitFlaggedRowRun prior true tail work₂
        input output buffer₁ buffer₂ test current.2
      have emit := compatibilityEdges_emitCompatibleEdgeRun current.2 prior.2
        input tail ((encodeIndexedOccurrenceEntry prior).reverse ++ work₂)
        output (some .tick) buffer₂ test
      have clear := compatibilityEdges_clearLowerRun prior.2 input tail
        ((encodeIndexedOccurrenceEntry prior).reverse ++ work₂)
        (encodeCliqueEdge (prior.2, current.2) ++ output)
        (some .tick) buffer₂ false current.2
      let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesEmitFlaggedRowSteps prior)
        (compatibilityEdgesEmitCompatibleEdgeSteps current.2 prior.2)
        _ _ _ (by
          simpa [encodeFlaggedOccurrenceEntry, compatible] using scan) emit
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ (prior.2 + 1) _ _ _ first clear
      simpa [compatible, encodeFlaggedOccurrenceEntry,
        encodeCompatibleOccurrenceEdge,
        compatibilityEdgesEmitPriorRowSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Reverse physical row family accumulated on work two by emission. -/
def encodeReversedOccurrenceEntries
    (entries : List (IndexedOccurrence × Nat)) : List UnaryFrameSym :=
  entries.flatMap fun entry => (encodeIndexedOccurrenceEntry entry).reverse

/-- Optional compatible edge family in explicit enumeration order. -/
def encodeCompatibleOccurrenceEdges
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List CliqueSym :=
  priors.flatMap (encodeCompatibleOccurrenceEdge current)

/-- Exact accumulated budget for emitting a flagged prior-row family. -/
def compatibilityEdgesEmitPriorRowsSteps
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : Nat :=
  (priors.map (compatibilityEdgesEmitPriorRowSteps current)).sum

/-- Final test register after a possibly empty emitted row family. -/
def compatibilityEdgesEmitPriorRowsFinalTest
    (initial : Bool) (priors : List (IndexedOccurrence × Nat)) : Bool :=
  match priors with
  | [] => initial
  | _ :: _ => false

/-- Every flagged prior row is consumed.  Compatible edges and reversed
physical rows accumulate in reverse family order, matching stack semantics. -/
def compatibilityEdges_emitPriorRowsRun
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (work₂ input : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    Σ finalBuffer₁ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .emitStart buffer₁ buffer₂ test input output
          (encodeFlaggedOccurrenceEntries current priors) work₂ current.2 0 0)
        (some (compatibilityEdgesCfg .emitStart finalBuffer₁ buffer₂
          (compatibilityEdgesEmitPriorRowsFinalTest test priors)
          input (encodeCompatibleOccurrenceEdges current priors.reverse ++ output)
          [] (encodeReversedOccurrenceEntries priors.reverse ++ work₂)
          current.2 0 0))
        (compatibilityEdgesEmitPriorRowsSteps current priors) := by
  induction priors generalizing buffer₁ test work₂ output with
  | nil =>
      exact ⟨buffer₁, ⟨⟨0, by
        simp [encodeFlaggedOccurrenceEntries, encodeCompatibleOccurrenceEdges,
          encodeReversedOccurrenceEntries,
          compatibilityEdgesEmitPriorRowsFinalTest]⟩, le_rfl⟩⟩
  | cons prior priors ih =>
      let remaining := encodeFlaggedOccurrenceEntries current priors
      have first := compatibilityEdges_emitPriorRowRun current prior remaining
        work₂ input output buffer₁ buffer₂ test
      rcases ih
          (buffer₁ := some (if indexedOccurrencesCompatibleCode current prior
            then .tick else .separator))
          (test := false)
          (work₂ := (encodeIndexedOccurrenceEntry prior).reverse ++ work₂)
          (output := encodeCompatibleOccurrenceEdge current prior ++ output) with
        ⟨finalBuffer₁, rest⟩
      refine ⟨finalBuffer₁, ?_⟩
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesEmitPriorRowSteps current prior)
        (compatibilityEdgesEmitPriorRowsSteps current priors) _ _ _ (by
          simpa [remaining, encodeFlaggedOccurrenceEntries,
            List.append_assoc] using first) rest
      have finalTest_eq :
          compatibilityEdgesEmitPriorRowsFinalTest false priors = false := by
        cases priors <;> rfl
      have consFinalTest_eq :
          compatibilityEdgesEmitPriorRowsFinalTest test (prior :: priors) =
            false := rfl
      simpa [remaining, encodeFlaggedOccurrenceEntries,
        encodeCompatibleOccurrenceEdges, encodeReversedOccurrenceEntries,
        compatibilityEdgesEmitPriorRowsSteps,
        finalTest_eq, consFinalTest_eq,
        List.reverse_cons,
        List.flatMap_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
