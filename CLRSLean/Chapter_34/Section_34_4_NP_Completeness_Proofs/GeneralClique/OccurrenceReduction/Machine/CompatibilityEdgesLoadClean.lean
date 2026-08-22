import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesSemantics

/-!
# Occurrence compatibility edges: clean loading boundary

The low-level loader theorem exposes its final second buffer existentially.
This file records the stronger invariant used by the full controller: when
loading starts with that buffer empty, every completed row leaves it empty.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private def compatibilityEdges_loadRowCleanRun
    (entry : IndexedOccurrence × Nat)
    (tail work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .load buffer₁ none test
        (encodeIndexedOccurrenceEntry entry ++ tail)
        output work₁ [] upper clause variableCount)
      (some (compatibilityEdgesCfg .load (some .frameEnd) none test
        tail output (encodeIndexedOccurrenceEntry entry ++ work₁) []
        upper clause variableCount))
      (compatibilityEdgesLoadRowSteps entry) := by
  exact (compatibilityEdges_loadRowRun entry tail work₁ output buffer₁ none
    test upper clause variableCount).2

/-- Loading a complete row family from an empty second buffer preserves that
clean buffer invariant and reverses only the row order. -/
def compatibilityEdges_loadRowsCleanRun
    (entries : List (IndexedOccurrence × Nat))
    (tail work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCount : Nat) :
    Σ finalBuffer₁,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .load buffer₁ none test
          (encodeIndexedOccurrenceEntries entries ++ tail)
          output work₁ [] upper clause variableCount)
        (some (compatibilityEdgesCfg .load finalBuffer₁ none test
          tail output
          (encodeIndexedOccurrenceEntries entries.reverse ++ work₁) []
          upper clause variableCount))
        (compatibilityEdgesLoadRowsSteps entries) := by
  induction entries generalizing buffer₁ work₁ with
  | nil =>
      exact ⟨buffer₁, ⟨⟨0, by
        simp [encodeIndexedOccurrenceEntries]⟩, le_rfl⟩⟩
  | cons entry entries ih =>
      let remaining := encodeIndexedOccurrenceEntries entries ++ tail
      have first := compatibilityEdges_loadRowCleanRun entry remaining work₁
        output buffer₁ test upper clause variableCount
      rcases ih (buffer₁ := some .frameEnd)
          (work₁ := encodeIndexedOccurrenceEntry entry ++ work₁) with
        ⟨finalBuffer₁, rest⟩
      refine ⟨finalBuffer₁, ?_⟩
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesLoadRowSteps entry)
        (compatibilityEdgesLoadRowsSteps entries) _ _ _ first rest
      simpa [remaining, encodeIndexedOccurrenceEntries,
        compatibilityEdgesLoadRowsSteps, List.reverse_cons,
        List.flatMap_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Loading the canonical occurrence rows reaches an outer-loop boundary
with both controller buffers and every counter clean. -/
def compatibilityEdges_loadCanonicalCleanRun (formula : CNF) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (initialCfg compatibilityEdgesProgram
        (encodeIndexedOccurrenceRows formula))
      (some (compatibilityEdgesCfg .outer none none false [] []
        (encodeIndexedOccurrenceEntries
          (indexedOccurrences formula).zipIdx.reverse)
        [] 0 0 0))
      (compatibilityEdgesLoadRowsSteps
        (indexedOccurrences formula).zipIdx + 1) := by
  have hrows := compatibilityEdges_loadRowsCleanRun
    (indexedOccurrences formula).zipIdx [] [] [] none false 0 0 0
  rw [encodeIndexedOccurrenceEntries_zipIdx] at hrows
  rcases hrows with ⟨finalBuffer₁, loaded⟩
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .load finalBuffer₁ none false [] []
        (encodeIndexedOccurrenceEntries
          (indexedOccurrences formula).zipIdx.reverse) [] 0 0 0)
      (some (compatibilityEdgesCfg .outer none none false [] []
        (encodeIndexedOccurrenceEntries
          (indexedOccurrences formula).zipIdx.reverse) [] 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (compatibilityEdgesLoadRowsSteps (indexedOccurrences formula).zipIdx)
    1 _ _ _ loaded (by simpa using finish)
  simpa [initialCfg, compatibilityEdgesCfg, compatibilityEdgesProgram,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
