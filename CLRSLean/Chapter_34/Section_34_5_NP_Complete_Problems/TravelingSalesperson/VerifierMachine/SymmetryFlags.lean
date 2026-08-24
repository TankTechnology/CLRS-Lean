import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SelectionFlags

/-!
# Decision-TSP verifier: orientation-selection flags

After the diagonal prefix, the physical matrix stores the forward and reverse
orientation of every normalized vertex pair consecutively.  These two fixed
branches select the first and second field of every such pair.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.SymmetryFlags

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def firstPairFlags (answers : List Bool) : List Bool :=
  answers.flatMap fun _ => [true, false]

def secondPairFlags (answers : List Bool) : List Bool :=
  answers.flatMap fun _ => [false, true]

def firstFlags (input : RawInput) : List Bool :=
  SelectionFlags.diagonalFlags input ++
    firstPairFlags (CycleMembership.membershipBits input)

def secondFlags (input : RawInput) : List Bool :=
  SelectionFlags.diagonalFlags input ++
    secondPairFlags (CycleMembership.membershipBits input)

private def firstBody : LoopBody Bool Bool where
  emit := fun _ => [true, false]
  cost := fun _ => 2
  emit_length_le_cost := by intro answer; rfl

private def secondBody : LoopBody Bool Bool where
  emit := fun _ => [false, true]
  cost := fun _ => 2
  emit_length_le_cost := by intro answer; rfl

private noncomputable def firstPairFlagsComputableInPolyTime :
    TM2ComputableInPolyTime id id firstPairFlags := by
  change TM2ComputableInPolyTime id id
    (fun answers : List Bool => answers.flatMap firstBody.emit)
  exact boundedLoop_computableInPolyTime firstBody

private noncomputable def secondPairFlagsComputableInPolyTime :
    TM2ComputableInPolyTime id id secondPairFlags := by
  change TM2ComputableInPolyTime id id
    (fun answers : List Bool => answers.flatMap secondBody.emit)
  exact boundedLoop_computableInPolyTime secondBody

private noncomputable def firstTailComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => firstPairFlags (CycleMembership.membershipBits input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    CycleMembership.membershipBitsComputableInPolyTime
    firstPairFlagsComputableInPolyTime
  change TM2ComputableInPolyTime CycleMembership.rawEncoding id
    (fun input => firstPairFlags (CycleMembership.membershipBits input))
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def secondTailComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => secondPairFlags (CycleMembership.membershipBits input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    CycleMembership.membershipBitsComputableInPolyTime
    secondPairFlagsComputableInPolyTime
  change TM2ComputableInPolyTime CycleMembership.rawEncoding id
    (fun input => secondPairFlags (CycleMembership.membershipBits input))
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

noncomputable def firstFlagsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id firstFlags := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeBoolPair decodeBoolPair decode_encodeBoolPair
    SelectionFlags.diagonalFlagsComputableInPolyTime
    firstTailComputableInPolyTime

noncomputable def secondFlagsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id secondFlags := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeBoolPair decodeBoolPair decode_encodeBoolPair
    SelectionFlags.diagonalFlagsComputableInPolyTime
    secondTailComputableInPolyTime

private theorem flatMap_constant_after_map {α β γ : Type}
    (values : List α) (f : α → β) (output : List γ) :
    (values.map f).flatMap (fun _ => output) =
      values.flatMap (fun _ => output) := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [ih]

@[simp] theorem firstFlags_encode (vertices : List Nat) (data : TSPData) :
    firstFlags (UnaryCertificate.encode vertices, encodeTSPData data) =
      List.replicate vertices.length false ++
        (vertexCoverNormalizedPairs vertices.length).flatMap
          (fun _ => [true, false]) := by
  rw [firstFlags, SelectionFlags.diagonalFlags_encode,
    CycleMembership.membershipBits_encode]
  exact congrArg (List.replicate vertices.length false ++ ·)
    (flatMap_constant_after_map _ _ [true, false])

@[simp] theorem secondFlags_encode (vertices : List Nat) (data : TSPData) :
    secondFlags (UnaryCertificate.encode vertices, encodeTSPData data) =
      List.replicate vertices.length false ++
        (vertexCoverNormalizedPairs vertices.length).flatMap
          (fun _ => [false, true]) := by
  rw [secondFlags, SelectionFlags.diagonalFlags_encode,
    CycleMembership.membershipBits_encode]
  exact congrArg (List.replicate vertices.length false ++ ·)
    (flatMap_constant_after_map _ _ [false, true])

end CLRS.Chapter34.Turing.TSPVerifier.SymmetryFlags
