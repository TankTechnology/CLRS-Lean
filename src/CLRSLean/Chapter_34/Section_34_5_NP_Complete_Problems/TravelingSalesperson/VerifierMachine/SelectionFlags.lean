import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.CycleMembership
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection

/-!
# Decision-TSP verifier: matrix-aligned selection flags

No valid tour with at least three distinct vertices uses a diagonal matrix
cell.  The remaining matrix fields occur in two orientations per normalized
pair, so each batch membership bit is duplicated.  The resulting stream is
aligned with the complete physical weight table.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.SelectionFlags

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def diagonalFlags (input : RawInput) : List Bool :=
  (FieldCount.certificateTicks input.1).map fun _ => false

def duplicateFlags (flags : List Bool) : List Bool :=
  flags.flatMap fun flag => [flag, flag]

def selectionFlags (input : RawInput) : List Bool :=
  diagonalFlags input ++ duplicateFlags (CycleMembership.membershipBits input)

private noncomputable def certificateProjection :
    TM2ComputableInPolyTime rawEncoding id Prod.fst := by
  let machine := PairFirstProjection.computableInPolyTime TSPSym
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa [rawEncoding, UnaryBaseInput.rawEncoding,
          StructuralChecks.rawEncoding] using machine.outputsFun input }

noncomputable def diagonalFlagsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id diagonalFlags := by
  let countedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    certificateProjection FieldCount.certificateTicksComputableInPolyTime
  let mappedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice countedExists)
    (listMap_computableInPolyTime (fun _ : Bool => false))
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => (FieldCount.certificateTicks input.1).map fun _ => false)
  simpa only [Function.comp_def] using Classical.choice mappedExists

private def duplicateBody : LoopBody Bool Bool where
  emit := fun flag => [flag, flag]
  cost := fun _ => 2
  emit_length_le_cost := by intro flag; simp

noncomputable def duplicateFlagsComputableInPolyTime :
    TM2ComputableInPolyTime id id duplicateFlags := by
  change TM2ComputableInPolyTime id id
    (fun flags : List Bool => flags.flatMap duplicateBody.emit)
  exact boundedLoop_computableInPolyTime duplicateBody

private noncomputable def duplicatedMembershipComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => duplicateFlags (CycleMembership.membershipBits input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    CycleMembership.membershipBitsComputableInPolyTime
    duplicateFlagsComputableInPolyTime
  change TM2ComputableInPolyTime CycleMembership.rawEncoding id
    (fun input => duplicateFlags (CycleMembership.membershipBits input))
  simpa only [Function.comp_def] using Classical.choice composed

private def encodeBoolPair : Bool → UnaryFrameSym × UnaryFrameSym
  | false => (.tick, .separator)
  | true => (.separator, .tick)

private def decodeBoolPair : UnaryFrameSym → UnaryFrameSym → Bool
  | .separator, .tick => true
  | _, _ => false

private theorem decode_encodeBoolPair (flag : Bool) :
    decodeBoolPair (encodeBoolPair flag).1 (encodeBoolPair flag).2 = flag := by
  cases flag <;> rfl

/-- A fixed polynomial-time machine emits exactly one Boolean per physical
matrix field. -/
noncomputable def selectionFlagsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id selectionFlags := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeBoolPair decodeBoolPair decode_encodeBoolPair
    diagonalFlagsComputableInPolyTime duplicatedMembershipComputableInPolyTime

@[simp] theorem diagonalFlags_encode (vertices : List Nat) (data : TSPData) :
    diagonalFlags
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      List.replicate vertices.length false := by
  simp [diagonalFlags]

@[simp] theorem selectionFlags_encode (vertices : List Nat) (data : TSPData) :
    selectionFlags
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      List.replicate vertices.length false ++
        ((vertexCoverNormalizedPairs vertices.length).map fun edge =>
          decide (edge ∈
            (HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices).map
              GeneralCliqueVerifier.QueryNormalizer.normalizeQuery)).flatMap
                fun flag => [flag, flag] := by
  simp [selectionFlags, duplicateFlags]

end CLRS.Chapter34.Turing.TSPVerifier.SelectionFlags
