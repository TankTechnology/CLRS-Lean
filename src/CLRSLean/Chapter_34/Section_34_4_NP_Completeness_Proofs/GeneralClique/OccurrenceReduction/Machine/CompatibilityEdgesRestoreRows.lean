import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRow
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: restore every tagged row

The tagged row family is restored to work one in forward order.  Every row is
followed by a one-symbol compatibility flag, and the controller reaches the
edge-emission entry with work two empty.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Forward occurrence row followed by its emission flag. -/
def encodeFlaggedOccurrenceEntry
    (current prior : IndexedOccurrence × Nat) : List UnaryFrameSym :=
  encodeIndexedOccurrenceEntry prior ++
    [if indexedOccurrencesCompatibleCode current prior then
      .tick else .separator]

/-- Forward flagged row family consumed by the emission pass. -/
def encodeFlaggedOccurrenceEntries
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List UnaryFrameSym :=
  priors.flatMap (encodeFlaggedOccurrenceEntry current)

/-- Exact family-restoration budget, including one boundary pop per row and
the final empty-stack transition. -/
def compatibilityEdgesRestoreTaggedRowsSteps
    (priors : List (IndexedOccurrence × Nat)) : Nat :=
  (priors.map (fun prior =>
    compatibilityEdgesRestoreTaggedRowSteps prior + 1)).sum + 1

private def compatibilityEdges_restoreTaggedRowsFromVertexRun
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (input work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
          input output work₁ (encodeTaggedOccurrenceEntries current priors)
          upper 0 0)
        (some (compatibilityEdgesCfg .emitStart buffer₁ finalBuffer₂ test
          input output
          (encodeFlaggedOccurrenceEntries current priors.reverse ++ work₁)
          [] upper 0 0))
        (compatibilityEdgesRestoreTaggedRowsSteps priors) := by
  induction priors generalizing buffer₂ work₁ with
  | nil =>
      exact ⟨none, ⟨⟨1, by
        simp [flip, encodeTaggedOccurrenceEntries,
          encodeFlaggedOccurrenceEntries, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩⟩
  | cons prior priors ih =>
      let compatible := indexedOccurrencesCompatibleCode current prior
      let taggedTail := encodeTaggedOccurrenceEntries current priors
      have boundary : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
            input output work₁
            (encodeTaggedOccurrenceEntry current prior ++ taggedTail)
            upper 0 0)
          (some (compatibilityEdgesCfg .taggedRestoreFlag buffer₁
            (some .separator) test input output work₁
            ((if compatible then .tick else .frameEnd) ::
              (encodeIndexedOccurrenceEntry prior).reverse ++ taggedTail)
            upper 0 0)) 1 := by
        exact ⟨⟨1, by
          simp [flip, compatible, encodeTaggedOccurrenceEntry,
            encodeCompatibilityTag, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      rcases compatibilityEdges_restoreTaggedRowRun prior compatible input
          work₁ taggedTail output buffer₁ (some .separator) test upper with
        ⟨afterRowBuffer₂, rowRun⟩
      rcases ih (buffer₂ := afterRowBuffer₂)
          (work₁ := encodeFlaggedOccurrenceEntry current prior ++ work₁) with
        ⟨finalBuffer₂, rest⟩
      refine ⟨finalBuffer₂, ?_⟩
      let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (compatibilityEdgesRestoreTaggedRowSteps prior) _ _ _ boundary (by
          simpa [compatible, encodeFlaggedOccurrenceEntry] using rowRun)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ (compatibilityEdgesRestoreTaggedRowsSteps priors) _ _ _ first (by
          simpa [taggedTail, encodeFlaggedOccurrenceEntry,
            List.append_assoc] using rest)
      simpa [taggedTail, encodeTaggedOccurrenceEntries,
        encodeFlaggedOccurrenceEntry, encodeFlaggedOccurrenceEntries,
        compatibilityEdgesRestoreTaggedRowsSteps,
        List.reverse_cons, List.flatMap_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- The complete tagged family is restored from the cleanup entry to the
emission entry, with exact forward row order and compatibility flags. -/
def compatibilityEdges_restoreTaggedRowsRun
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (input work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂ test
          input output work₁ (encodeTaggedOccurrenceEntries current priors)
          upper 0 0)
        (some (compatibilityEdgesCfg .emitStart buffer₁ finalBuffer₂ test
          input output
          (encodeFlaggedOccurrenceEntries current priors.reverse ++ work₁)
          [] upper 0 0))
        (compatibilityEdgesRestoreTaggedRowsSteps priors) := by
  cases priors with
  | nil =>
      exact ⟨none, ⟨⟨1, by
        simp [flip, encodeTaggedOccurrenceEntries,
          encodeFlaggedOccurrenceEntries, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩⟩
  | cons prior priors =>
      let compatible := indexedOccurrencesCompatibleCode current prior
      let taggedTail := encodeTaggedOccurrenceEntries current priors
      have boundary : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .taggedRestoreStart buffer₁ buffer₂ test
            input output work₁
            (encodeTaggedOccurrenceEntry current prior ++ taggedTail)
            upper 0 0)
          (some (compatibilityEdgesCfg .taggedRestoreFlag buffer₁
            (some .separator) test input output work₁
            ((if compatible then .tick else .frameEnd) ::
              (encodeIndexedOccurrenceEntry prior).reverse ++ taggedTail)
            upper 0 0)) 1 := by
        exact ⟨⟨1, by
          simp [flip, compatible, encodeTaggedOccurrenceEntry,
            encodeCompatibilityTag, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      rcases compatibilityEdges_restoreTaggedRowRun prior compatible input
          work₁ taggedTail output buffer₁ (some .separator) test upper with
        ⟨afterRowBuffer₂, rowRun⟩
      rcases compatibilityEdges_restoreTaggedRowsFromVertexRun current priors
          input (encodeFlaggedOccurrenceEntry current prior ++ work₁) output
          buffer₁ afterRowBuffer₂ test upper with
        ⟨finalBuffer₂, rest⟩
      refine ⟨finalBuffer₂, ?_⟩
      let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (compatibilityEdgesRestoreTaggedRowSteps prior) _ _ _ boundary (by
          simpa [compatible, encodeFlaggedOccurrenceEntry] using rowRun)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ (compatibilityEdgesRestoreTaggedRowsSteps priors) _ _ _ first (by
          simpa [taggedTail, encodeFlaggedOccurrenceEntry,
            List.append_assoc] using rest)
      simpa [taggedTail, encodeTaggedOccurrenceEntries,
        encodeFlaggedOccurrenceEntry, encodeFlaggedOccurrenceEntries,
        compatibilityEdgesRestoreTaggedRowsSteps,
        List.reverse_cons, List.flatMap_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
