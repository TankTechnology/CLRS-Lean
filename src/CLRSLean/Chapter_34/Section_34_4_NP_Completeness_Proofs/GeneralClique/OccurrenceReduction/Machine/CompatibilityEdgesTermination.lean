import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesLoadClean

/-!
# Occurrence compatibility edges: complete terminating run

The verified loader, all outer iterations, the empty-stack boundary, and the
successful halt are composed here into one formula-level controller theorem.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Exact step budget of the complete compatibility-edge controller on one
semantic formula. -/
def compatibilityEdgesSteps (formula : CNF) : Nat :=
  compatibilityEdgesLoadRowsSteps (indexedOccurrences formula).zipIdx +
    compatibilityEdgesOuterIterationsSteps
      (indexedOccurrences formula).zipIdx.reverse + 3

/-- The complete fixed controller consumes canonical occurrence rows, emits
exactly the canonical occurrence-graph edge suffix, clears all scratch state,
and halts successfully. -/
def compatibilityEdges_run (formula : CNF) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (initialCfg compatibilityEdgesProgram
        (encodeIndexedOccurrenceRows formula))
      (some (haltCfg compatibilityEdgesProgram
        (encodeOccurrenceCliqueEdges formula)))
      (compatibilityEdgesSteps formula) := by
  have loaded := compatibilityEdges_loadCanonicalCleanRun formula
  have iterations := compatibilityEdges_outerIterationsRun
    (indexedOccurrences formula).zipIdx.reverse []
  have stop : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer none none false []
        (encodeCompatibleOccurrenceIterations
          (indexedOccurrences formula).zipIdx.reverse)
        [] [] 0 0 0)
      (some (compatibilityEdgesCfg .halt none none false []
        (encodeCompatibleOccurrenceIterations
          (indexedOccurrences formula).zipIdx.reverse)
        [] [] 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have halt : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .halt none none false []
        (encodeCompatibleOccurrenceIterations
          (indexedOccurrences formula).zipIdx.reverse)
        [] [] 0 0 0)
      (some (haltCfg compatibilityEdgesProgram
        (encodeCompatibleOccurrenceIterations
          (indexedOccurrences formula).zipIdx.reverse))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (compatibilityEdgesLoadRowsSteps
      (indexedOccurrences formula).zipIdx + 1)
    (compatibilityEdgesOuterIterationsSteps
      (indexedOccurrences formula).zipIdx.reverse)
    _ _ _ loaded iterations
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ first (by simpa using stop)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second halt
  convert full using 1 <;>
    simp [compatibilityEdgesSteps,
      encodeCompatibleOccurrenceIterations_canonical]
  omega

end TMClique
end Turing
end Chapter34
end CLRS
