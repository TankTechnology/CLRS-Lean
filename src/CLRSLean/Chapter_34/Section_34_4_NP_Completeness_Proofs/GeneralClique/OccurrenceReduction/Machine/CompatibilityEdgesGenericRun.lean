import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesLoadClean

/-!
# Generic terminating run of the occurrence-row pair controller

The compatibility controller is useful beyond the 3-CNF occurrence graph.
This module exposes its actual reusable boundary: an arbitrary family of
four-field indexed-occurrence rows.  The earlier formula-specific theorem is
an immediate specialization of this run.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.TMClique

open PolyBuilder

/-- Exact step budget for the compatibility controller on an arbitrary
explicit row family. -/
def compatibilityEdgesEntriesSteps
    (entries : List (IndexedOccurrence × Nat)) : Nat :=
  compatibilityEdgesLoadRowsSteps entries +
    compatibilityEdgesOuterIterationsSteps entries.reverse + 3

/-- The fixed compatibility controller consumes any canonical four-field row
family, emits its compatible endpoint pairs, clears all scratch state, and
halts. -/
def compatibilityEdges_entriesRun
    (entries : List (IndexedOccurrence × Nat)) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (initialCfg compatibilityEdgesProgram
        (encodeIndexedOccurrenceEntries entries))
      (some (haltCfg compatibilityEdgesProgram
        (encodeCompatibleOccurrenceIterations entries.reverse)))
      (compatibilityEdgesEntriesSteps entries) := by
  rcases compatibilityEdges_loadRowsCleanRun
      entries [] [] [] none false 0 0 0 with
    ⟨finalBuffer₁, loadedRows⟩
  have enterOuter : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .load finalBuffer₁ none false [] []
        (encodeIndexedOccurrenceEntries entries.reverse) [] 0 0 0)
      (some (compatibilityEdgesCfg .outer none none false [] []
        (encodeIndexedOccurrenceEntries entries.reverse) [] 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have loaded : EvalsToInTime (step compatibilityEdgesProgram)
      (initialCfg compatibilityEdgesProgram
        (encodeIndexedOccurrenceEntries entries))
      (some (compatibilityEdgesCfg .outer none none false [] []
        (encodeIndexedOccurrenceEntries entries.reverse) [] 0 0 0))
      (compatibilityEdgesLoadRowsSteps entries + 1) := by
    let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
      (compatibilityEdgesLoadRowsSteps entries) 1 _ _ _
      loadedRows (by simpa using enterOuter)
    simpa [initialCfg, compatibilityEdgesCfg, compatibilityEdgesProgram,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  have iterations := compatibilityEdges_outerIterationsRun
    entries.reverse []
  have stop : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer none none false []
        (encodeCompatibleOccurrenceIterations entries.reverse)
        [] [] 0 0 0)
      (some (compatibilityEdgesCfg .halt none none false []
        (encodeCompatibleOccurrenceIterations entries.reverse)
        [] [] 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have halt : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .halt none none false []
        (encodeCompatibleOccurrenceIterations entries.reverse)
        [] [] 0 0 0)
      (some (haltCfg compatibilityEdgesProgram
        (encodeCompatibleOccurrenceIterations entries.reverse))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let afterIterations := EvalsToInTime.trans
    (step compatibilityEdgesProgram)
    (compatibilityEdgesLoadRowsSteps entries + 1)
    (compatibilityEdgesOuterIterationsSteps entries.reverse)
    _ _ _ loaded iterations
  let stopped := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ afterIterations (by simpa using stop)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ stopped halt
  convert full using 1
  simp only [compatibilityEdgesEntriesSteps]
  omega

end CLRS.Chapter34.Turing.TMClique
