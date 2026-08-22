import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesIteration

/-!
# Occurrence compatibility edges: all outer iterations

This file iterates the verified one-row outer loop over an arbitrary family of
indexed occurrences.  The formula-specific identification with the canonical
normalized edge enumeration is deliberately kept for a later semantic file.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Edge encoding accumulated by exhausting an explicitly ordered outer-loop
row family.  Later iterations prepend their edges, exactly as the output stack
does. -/
def encodeCompatibleOccurrenceIterations :
    List (IndexedOccurrence × Nat) → List CliqueSym
  | [] => []
  | current :: priors =>
      encodeCompatibleOccurrenceIterations priors ++
        encodeCompatibleOccurrenceEdges current priors.reverse

/-- Exact accumulated budget for exhausting every outer-loop row. -/
def compatibilityEdgesOuterIterationsSteps :
    List (IndexedOccurrence × Nat) → Nat
  | [] => 0
  | current :: priors =>
      compatibilityEdgesOuterIterationSteps current priors +
        compatibilityEdgesOuterIterationsSteps priors

/-- Starting from a clean outer-loop boundary, all rows are consumed, their
compatible edges are accumulated, and the controller returns to the same
clean boundary with both work stacks empty. -/
def compatibilityEdges_outerIterationsRun
    (entries : List (IndexedOccurrence × Nat)) (output : List CliqueSym) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer none none false [] output
        (encodeIndexedOccurrenceEntries entries) [] 0 0 0)
      (some (compatibilityEdgesCfg .outer none none false []
        (encodeCompatibleOccurrenceIterations entries ++ output)
        [] [] 0 0 0))
      (compatibilityEdgesOuterIterationsSteps entries) := by
  induction entries generalizing output with
  | nil =>
      exact ⟨⟨0, by
        simp [encodeIndexedOccurrenceEntries,
          encodeCompatibleOccurrenceIterations]⟩, le_rfl⟩
  | cons current priors ih =>
      have first := compatibilityEdges_outerIterationRun current priors output
        none none false
      have rest := ih
        (output := encodeCompatibleOccurrenceEdges current priors.reverse ++
          output)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesOuterIterationSteps current priors)
        (compatibilityEdgesOuterIterationsSteps priors) _ _ _ first rest
      simpa [encodeIndexedOccurrenceEntries,
        encodeCompatibleOccurrenceIterations,
        compatibilityEdgesOuterIterationsSteps, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
