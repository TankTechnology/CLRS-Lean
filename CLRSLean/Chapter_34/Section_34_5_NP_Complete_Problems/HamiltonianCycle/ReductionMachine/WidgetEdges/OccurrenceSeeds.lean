import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.WidgetEdges.Source
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleMapSource

/-!
# VERTEX-COVER to HAM-CYCLE machine: gadget-occurrence seeds

The generic affine triple progression expands the source descriptor into the
row-major runtime triples `(i, 0, 0)`.  We expose the result through the
canonical seed-family encoder expected by the next fixed affine-map stage.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges

open _root_.Turing
open PolyBuilder

/-- Convert one progression row to the seed interface of the fixed affine-map
source. -/
def rowSeed (row : Nat × Nat × Nat) : AffineUnaryTripleSeed where
  first := row.1
  second := row.2.1
  third := row.2.2

/-- Runtime occurrence seeds generated from an arbitrary source string. -/
def occurrenceSeeds (input : List CliqueSym) : List AffineUnaryTripleSeed :=
  (affineUnaryTripleProgressionRows (Source.progression input)).map rowSeed

/-- Raw delimiter stream emitted by the progression controller. -/
def occurrenceSeedStream (input : List CliqueSym) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFrameStream (Source.progression input)

private theorem encodeSeedFamily_map_rowSeed
    (rows : List (Nat × Nat × Nat)) :
    encodeAffineUnaryTripleSeedFamily (rows.map rowSeed) =
      rows.flatMap fun row => affineUnaryTripleRowValues row |> encodeUnaryFrame := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [encodeAffineUnaryTripleSeedFamily, rowSeed,
        encodeAffineUnaryTripleSeed, affineUnaryTripleRowValues, ih]

/-- The progression output is exactly the seed-family representation, on all
raw inputs. -/
theorem occurrenceSeedStream_eq_encode (input : List CliqueSym) :
    occurrenceSeedStream input =
      encodeAffineUnaryTripleSeedFamily (occurrenceSeeds input) := by
  unfold occurrenceSeedStream occurrenceSeeds
  rw [encodeSeedFamily_map_rowSeed]
  rfl

/-- A fixed polynomial-time TM2 computes the occurrence seed family directly
from the raw source alphabet. -/
noncomputable def occurrenceSeedsComputableInPolyTime :
    TM2ComputableInPolyTime id encodeAffineUnaryTripleSeedFamily
      occurrenceSeeds := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    Source.computableInPolyTime
    affineUnaryTripleProgressionFrameStream_computableInPolyTime
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        rw [← occurrenceSeedStream_eq_encode input]
        simpa only [Function.comp_def, occurrenceSeedStream, id_eq] using
          raw.outputsFun input }

/-- The canonical occurrence seed at index `i`. -/
def occurrenceSeed (i : Nat) : AffineUnaryTripleSeed where
  first := i
  second := 0
  third := 0

/-- On canonical instances the seed family is exactly `(0,0,0), …,
(edgeCount-1,0,0)` in source-occurrence order. -/
theorem occurrenceSeeds_encode (I : VertexCoverInstance) :
    occurrenceSeeds (encodeVertexCoverInstance I) =
      (List.range I.edges.length).map occurrenceSeed := by
  unfold occurrenceSeeds
  rw [Source.progression_encode,
    affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    simp [rowSeed, occurrenceSeed]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.WidgetEdges
