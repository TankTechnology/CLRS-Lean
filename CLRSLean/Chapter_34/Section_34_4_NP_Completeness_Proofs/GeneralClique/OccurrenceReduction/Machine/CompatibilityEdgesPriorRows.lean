import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesPriorRow
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: all prior rows

This file iterates the verified one-row scan across the complete family below
one current occurrence.  The resulting reversed rows carry their exact
compatibility tags and the controller reaches the counter-cleanup boundary.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- One reversed prior row together with its compatibility tag. -/
def encodeTaggedOccurrenceEntry
    (current prior : IndexedOccurrence × Nat) : List UnaryFrameSym :=
  encodeCompatibilityTag (indexedOccurrencesCompatibleCode current prior) ++
    (encodeIndexedOccurrenceEntry prior).reverse

/-- Tagged physical family used by the restoration and emission phases. -/
def encodeTaggedOccurrenceEntries
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : List UnaryFrameSym :=
  priors.flatMap (encodeTaggedOccurrenceEntry current)

/-- Exact accumulated budget for scanning every row below one current row. -/
def compatibilityEdgesPriorRowsSteps
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) : Nat :=
  (priors.map (compatibilityEdgesPriorRowSteps current)).sum

/-- Every prior row is scanned once.  Rows are moved to work two in reverse
family order, each row is reversed physically, and each receives the exact
Boolean compatibility tag. -/
def compatibilityEdges_priorRowsRun
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    Σ finalBuffer₁ : Option UnaryFrameSym,
      Σ finalBuffer₂ : Option UnaryFrameSym,
        Σ finalTest : Bool,
          EvalsToInTime (step compatibilityEdgesProgram)
            (compatibilityEdgesCfg
              (.priorStart (occurrencePolarityFlag current.1.literal))
              buffer₁ buffer₂ test [] output
              (encodeIndexedOccurrenceEntries priors ++ tail) work₂
              current.2 current.1.clauseIndex
              (occurrenceVariableCode current.1.literal))
            (some (compatibilityEdgesCfg
              (.priorStart (occurrencePolarityFlag current.1.literal))
              finalBuffer₁ finalBuffer₂ finalTest [] output tail
              (encodeTaggedOccurrenceEntries current priors.reverse ++ work₂)
              current.2 current.1.clauseIndex
              (occurrenceVariableCode current.1.literal)))
            (compatibilityEdgesPriorRowsSteps current priors) := by
  induction priors generalizing buffer₁ buffer₂ test work₂ with
  | nil =>
      exact ⟨buffer₁, buffer₂, test, ⟨⟨0, by
        simp [encodeIndexedOccurrenceEntries,
          encodeTaggedOccurrenceEntries]⟩, le_rfl⟩⟩
  | cons prior priors ih =>
      let remaining := encodeIndexedOccurrenceEntries priors ++ tail
      have first := compatibilityEdges_priorRowRun current prior remaining
        work₂ output buffer₁ buffer₂ test
      rcases ih (buffer₁ := some .frameEnd) (buffer₂ := none)
          (test := decide (occurrenceVariableCode prior.1.literal <
            occurrenceVariableCode current.1.literal))
          (work₂ := encodeTaggedOccurrenceEntry current prior ++ work₂) with
        ⟨finalBuffer₁, finalBuffer₂, finalTest, rest⟩
      refine ⟨finalBuffer₁, finalBuffer₂, finalTest, ?_⟩
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesPriorRowSteps current prior)
        (compatibilityEdgesPriorRowsSteps current priors) _ _ _ first rest
      simpa [remaining, encodeIndexedOccurrenceEntries,
        encodeTaggedOccurrenceEntries, encodeTaggedOccurrenceEntry,
        compatibilityEdgesPriorRowsSteps, List.reverse_cons,
        List.flatMap_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Once no prior row remains, the next controller step enters current-counter
cleanup and clears the stale work-one buffer. -/
def compatibilityEdges_priorRowsDoneRun
    (current : IndexedOccurrence × Nat)
    (work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag current.1.literal))
        buffer₁ buffer₂ test [] output [] work₂ current.2
        current.1.clauseIndex (occurrenceVariableCode current.1.literal))
      (some (compatibilityEdgesCfg .clearCurrentClause none buffer₂ test []
        output [] work₂ current.2 current.1.clauseIndex
        (occurrenceVariableCode current.1.literal))) 1 := by
  exact ⟨⟨1, by
    simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
      stepOp]⟩, le_rfl⟩

end TMClique
end Turing
end Chapter34
end CLRS
