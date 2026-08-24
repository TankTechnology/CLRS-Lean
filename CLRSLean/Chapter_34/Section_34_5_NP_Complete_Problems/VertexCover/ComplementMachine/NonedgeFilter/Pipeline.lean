import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.FilterInput
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Selector

/-!
# VERTEX-COVER complement machine: complete nonedge pipeline

This module composes candidate enumeration, repeated source-edge lookup, and
the fixed selector.  The resulting machine emits precisely the encoded edge
table of the graph complement.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter

open _root_.Turing
open PolyBuilder

def alignedInput (I : CliqueInstance) : Selector.AlignedInput :=
  ⟨(candidatePairs I, membershipBits I), by
    simp⟩

theorem alignedInputEncoding_eq_filterInput (I : CliqueInstance) :
    Selector.alignedInputEncoding (alignedInput I) = filterInput I := by
  rfl

/-- Typed view of the already-computed concrete filter input. -/
noncomputable def alignedInputComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance
      Selector.alignedInputEncoding alignedInput := by
  let raw := filterInputComputableInPolyTime
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun I => by
        have output := raw.outputsFun I
        rw [alignedInputEncoding_eq_filterInput]
        simpa using output }

def selectedCandidateStream (I : CliqueInstance) : List CliqueSym :=
  Selector.alignedSelectedStream (alignedInput I)

private theorem selectedEdges_membershipMap
    (source : List (Nat × Nat)) (edges : List (Nat × Nat)) :
    Selector.selectedEdges edges
        (edges.map fun edge => decide (edge ∈ source)) =
      edges.filter fun edge => edge ∉ source := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      by_cases hmem : edge ∈ source <;>
        simp [Selector.selectedEdges, hmem, ih]

theorem selectedCandidateStream_eq_complement (I : CliqueInstance) :
    selectedCandidateStream I =
      (vertexCoverComplementEdges I).flatMap encodeCliqueEdge := by
  simp only [selectedCandidateStream, Selector.alignedSelectedStream,
    alignedInput, Selector.selectedStream]
  rw [show membershipBits I =
      (candidatePairs I).map fun edge => decide (edge ∈ I.edges) by
    rfl]
  rw [selectedEdges_membershipMap]
  rw [← complementEdges_eq_filter]

/-- A fixed polynomial-time TM2 computes the exact serialized complement
edge table from the original canonical graph encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id
      (fun I => (vertexCoverComplementEdges I).flatMap encodeCliqueEdge) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    alignedInputComputableInPolyTime Selector.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simp only [Function.comp_apply, id_eq] at output
        have hsemantic := selectedCandidateStream_eq_complement I
        change Selector.alignedSelectedStream (alignedInput I) = _ at hsemantic
        rw [hsemantic] at output
        simpa [Function.comp_def] using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
