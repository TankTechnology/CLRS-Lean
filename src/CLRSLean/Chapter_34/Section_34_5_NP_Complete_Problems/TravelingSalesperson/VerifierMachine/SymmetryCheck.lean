import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SelectedWeightFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SymmetryFlags
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListPairEq

/-! # Decision-TSP verifier: symmetric weight-table check -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.SymmetryCheck

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def fieldBits (values : List Nat) : List (Option Bool) :=
  values.flatMap fun value => (encodeBinaryNat value).map some ++ [none]

def firstFields (input : RawInput) : List (Option Bool) :=
  SelectedWeightFields.selectedFieldsWith SymmetryFlags.firstFlags input

def secondFields (input : RawInput) : List (Option Bool) :=
  SelectedWeightFields.selectedFieldsWith SymmetryFlags.secondFlags input

def symmetryCheck (input : RawInput) : Bool :=
  decide (firstFields input = secondFields input)

private noncomputable def firstFieldsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id firstFields := by
  change TM2ComputableInPolyTime SelectedWeightFields.rawEncoding id
    (SelectedWeightFields.selectedFieldsWith SymmetryFlags.firstFlags)
  exact SelectedWeightFields.selectedFieldsWithComputableInPolyTime
    SymmetryFlags.firstFlagsComputableInPolyTime

private noncomputable def secondFieldsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id secondFields := by
  change TM2ComputableInPolyTime SelectedWeightFields.rawEncoding id
    (SelectedWeightFields.selectedFieldsWith SymmetryFlags.secondFlags)
  exact SelectedWeightFields.selectedFieldsWithComputableInPolyTime
    SymmetryFlags.secondFlagsComputableInPolyTime

private def leftPart (fields : List (Option Bool)) :
    List (Option (Option Bool)) := fields.map some

private def rightPart (fields : List (Option Bool)) :
    List (Option (Option Bool)) := none :: fields.map some

private def rightSpec : StatefulFlatMapSpec Bool (Option Bool)
    (Option (Option Bool)) where
  initial := false
  action started field :=
    if started then ([some field], true)
    else ([none, some field], true)
  finish started := if started then [] else [none]

private theorem rightStarted (fields : List (Option Bool)) :
    rewriteStatefulFlatMapFrom rightSpec true fields = fields.map some := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec] using congrArg (some field :: ·) ih

private theorem rightRewrite (fields : List (Option Bool)) :
    rewriteStatefulFlatMap rightSpec fields = rightPart fields := by
  cases fields with
  | nil => rfl
  | cons field fields =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec, rightPart] using
        congrArg (fun tail => none :: some field :: tail)
          (rightStarted fields)

private noncomputable def leftFormatterComputableInPolyTime :
    TM2ComputableInPolyTime id id leftPart :=
  listMap_computableInPolyTime some

private noncomputable def rightFormatterComputableInPolyTime :
    TM2ComputableInPolyTime id id rightPart := by
  let machine := statefulFlatMap_computableInPolyTime rightSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun fields => by
        have output := machine.outputsFun fields
        rw [rightRewrite] at output
        exact output }

private noncomputable def leftPartComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => leftPart (firstFields input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    firstFieldsComputableInPolyTime leftFormatterComputableInPolyTime
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def rightPartComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => rightPart (secondFields input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    secondFieldsComputableInPolyTime rightFormatterComputableInPolyTime
  simpa only [Function.comp_def] using Classical.choice composed

private def encodePairSymbol : Option (Option Bool) →
    UnaryFrameSym × UnaryFrameSym
  | none => (.tick, .tick)
  | some none => (.tick, .separator)
  | some (some false) => (.separator, .tick)
  | some (some true) => (.separator, .separator)

private def decodePairSymbol : UnaryFrameSym → UnaryFrameSym →
    Option (Option Bool)
  | .tick, .tick => none
  | .tick, .separator => some none
  | .separator, .tick => some (some false)
  | .separator, .separator => some (some true)
  | _, _ => none

private theorem decode_encodePairSymbol (symbol : Option (Option Bool)) :
    decodePairSymbol (encodePairSymbol symbol).1
      (encodePairSymbol symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some field => cases field <;> first | rfl | rename_i bit; cases bit <;> rfl

private noncomputable def pairComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun pair : List (Option Bool) × List (Option Bool) =>
        pairEncoding pair.1 pair.2)
      (fun input => (firstFields input, secondFields input)) := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodePairSymbol decodePairSymbol decode_encodePairSymbol
    leftPartComputableInPolyTime rightPartComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [pairEncoding, leftPart, rightPart, List.append_assoc] using output }

/-- One fixed polynomial-time machine verifies equality of every pair of
oppositely oriented off-diagonal fields. -/
noncomputable def symmetryCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      symmetryCheck := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    pairComputableInPolyTime (ListPairEq.computableInPolyTime (Option Bool))
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => decide (firstFields input = secondFields input))
  simpa only [Function.comp_def] using Classical.choice composed

private theorem selectCurrent_field (flag : Bool) (flags : List Bool)
    (bits : List Bool) (fields : List (Option Bool)) :
    SelectDelimitedFields.selectCurrent flag flags
        (bits.map some ++ none :: fields) =
      (if flag then bits.map some ++ [none] else []) ++
        SelectDelimitedFields.selectFields flags fields := by
  induction bits with
  | nil => cases flag <;> simp [SelectDelimitedFields.selectCurrent]
  | cons bit bits ih =>
      cases flag <;> simp [SelectDelimitedFields.selectCurrent, ih,
        List.append_assoc]

private theorem select_false_prefix (leading rest : List Nat)
    (flags : List Bool) :
    SelectDelimitedFields.selectFields
        (List.replicate leading.length false ++ flags)
        (fieldBits (leading ++ rest)) =
      SelectDelimitedFields.selectFields flags (fieldBits rest) := by
  induction leading with
  | nil => rfl
  | cons value leading ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        fieldBits, List.flatMap_cons, SelectDelimitedFields.selectFields,
        List.append_assoc]
      rw [selectCurrent_field]
      simpa [fieldBits] using ih

private theorem select_first_pairs {α : Type} (markers : List α)
    (weights : List Nat) (hlength : weights.length = 2 * markers.length) :
    SelectDelimitedFields.selectFields
        (markers.flatMap fun _ => [true, false]) (fieldBits weights) =
      fieldBits (TSPData.firstOrientations weights) := by
  induction markers generalizing weights with
  | nil =>
      cases weights with
      | nil => simp [fieldBits, TSPData.firstOrientations,
          SelectDelimitedFields.selectFields]
      | cons weight weights => simp at hlength
  | cons marker markers ih =>
      cases weights with
      | nil => simp only [List.length_nil, List.length_cons] at hlength; omega
      | cons forward weights =>
          cases weights with
          | nil => simp only [List.length_cons, List.length_nil] at hlength; omega
          | cons reverse rest =>
              have hrest : rest.length = 2 * markers.length := by
                simp only [List.length_cons] at hlength
                omega
              simp only [List.flatMap_cons, fieldBits,
                TSPData.firstOrientations, List.append_assoc,
                List.cons_append,
                SelectDelimitedFields.selectFields]
              rw [selectCurrent_field]
              simp only [ite_true, List.nil_append]
              rw [SelectDelimitedFields.selectFields, selectCurrent_field]
              simpa [Bool.false_eq_true, fieldBits, List.append_assoc] using
                ih rest hrest

private theorem select_second_pairs {α : Type} (markers : List α)
    (weights : List Nat) (hlength : weights.length = 2 * markers.length) :
    SelectDelimitedFields.selectFields
        (markers.flatMap fun _ => [false, true]) (fieldBits weights) =
      fieldBits (TSPData.secondOrientations weights) := by
  induction markers generalizing weights with
  | nil =>
      cases weights with
      | nil => simp [fieldBits, TSPData.secondOrientations,
          SelectDelimitedFields.selectFields]
      | cons weight weights => simp at hlength
  | cons marker markers ih =>
      cases weights with
      | nil => simp only [List.length_nil, List.length_cons] at hlength; omega
      | cons forward weights =>
          cases weights with
          | nil => simp only [List.length_cons, List.length_nil] at hlength; omega
          | cons reverse rest =>
              have hrest : rest.length = 2 * markers.length := by
                simp only [List.length_cons] at hlength
                omega
              simp only [List.flatMap_cons, fieldBits,
                TSPData.secondOrientations, List.append_assoc,
                List.cons_append,
                SelectDelimitedFields.selectFields]
              rw [selectCurrent_field]
              simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
              rw [SelectDelimitedFields.selectFields, selectCurrent_field]
              simpa [fieldBits, List.append_assoc] using ih rest hrest

private def restoreFields : Bool → List (Option Bool) → List TSPSym
  | _, [] => []
  | startsField, some bit :: rest =>
      (if startsField then [.numberMark, .bit bit] else [.bit bit]) ++
        restoreFields false rest
  | _, none :: rest => .fieldEnd :: restoreFields true rest

private theorem restoreFields_false (bits : List Bool)
    (rest : List (Option Bool)) :
    restoreFields false (bits.map some ++ none :: rest) =
      bits.map TSPSym.bit ++ .fieldEnd :: restoreFields true rest := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [restoreFields, ih]

private theorem restoreFields_field (value : Nat)
    (rest : List (Option Bool)) :
    restoreFields true
        ((encodeBinaryNat value).map some ++ none :: rest) =
      encodeTSPField value ++ restoreFields true rest := by
  have hnonempty : encodeBinaryNat value ≠ [] := by
    intro hempty
    have hpos := encodeBinaryNat_length_pos value
    simp [hempty] at hpos
  cases hbits : encodeBinaryNat value with
  | nil => exact (hnonempty hbits).elim
  | cons bit bits =>
      simp only [List.map_cons, List.cons_append, restoreFields,
        ite_true]
      rw [restoreFields_false]
      simp [encodeTSPField, hbits]

private theorem restoreFields_fieldBits (values : List Nat) :
    restoreFields true (fieldBits values) = encodeTSPFields values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change restoreFields true
          ((encodeBinaryNat value).map some ++ [none] ++ fieldBits values) =
        encodeTSPField value ++ encodeTSPFields values
      simp only [List.append_assoc, List.singleton_append]
      rw [restoreFields_field, ih]

private theorem fieldBits_injective : Function.Injective fieldBits := by
  intro left right heq
  have restored := congrArg (restoreFields true) heq
  rw [restoreFields_fieldBits, restoreFields_fieldBits] at restored
  exact encodeTSPFields_injective restored

private theorem tail_length (data : TSPData)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    (data.weights.drop data.vertexCount).length =
      2 * (tspNormalizedPairs data.vertexCount).length := by
  rw [List.length_drop, hshape]
  have hpairs := tspNormalizedPairs_length_identity data.vertexCount
  omega

private theorem vertexCount_le_weights_length (data : TSPData)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    data.vertexCount ≤ data.weights.length := by
  rw [hshape]
  cases data.vertexCount <;> nlinarith

theorem firstFields_encode (vertices : List Nat) (data : TSPData)
    (hcount : vertices.length = data.vertexCount)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    firstFields (UnaryCertificate.encode vertices, encodeTSPData data) =
      fieldBits (TSPData.firstOrientations
        (data.weights.drop data.vertexCount)) := by
  rw [firstFields, SelectedWeightFields.selectedFieldsWith,
    SymmetryFlags.firstFlags_encode, WeightBitFields.fields_encode, hcount]
  change SelectDelimitedFields.selectFields
      (List.replicate data.vertexCount false ++
        (vertexCoverNormalizedPairs data.vertexCount).flatMap
          (fun _ => [true, false]))
      (fieldBits data.weights) =
    fieldBits (TSPData.firstOrientations
      (data.weights.drop data.vertexCount))
  let leading := data.weights.take data.vertexCount
  let rest := data.weights.drop data.vertexCount
  have hsplit : leading ++ rest = data.weights := by
    exact List.take_append_drop _ _
  have hleading : leading.length = data.vertexCount := by
    simp [leading, vertexCount_le_weights_length data hshape]
  have hrest : rest.length =
      2 * (vertexCoverNormalizedPairs data.vertexCount).length := by
    have hpairs : tspNormalizedPairs data.vertexCount =
        vertexCoverNormalizedPairs data.vertexCount := by
      induction data.vertexCount with
      | zero => rfl
      | succ n ih =>
          simp only [tspNormalizedPairs, vertexCoverNormalizedPairs, ih]
    simpa [rest, hpairs] using tail_length data hshape
  rw [← hsplit, ← hleading]
  rw [select_false_prefix]
  simpa [hleading] using select_first_pairs _ rest hrest

theorem secondFields_encode (vertices : List Nat) (data : TSPData)
    (hcount : vertices.length = data.vertexCount)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    secondFields (UnaryCertificate.encode vertices, encodeTSPData data) =
      fieldBits (TSPData.secondOrientations
        (data.weights.drop data.vertexCount)) := by
  rw [secondFields, SelectedWeightFields.selectedFieldsWith,
    SymmetryFlags.secondFlags_encode, WeightBitFields.fields_encode, hcount]
  change SelectDelimitedFields.selectFields
      (List.replicate data.vertexCount false ++
        (vertexCoverNormalizedPairs data.vertexCount).flatMap
          (fun _ => [false, true]))
      (fieldBits data.weights) =
    fieldBits (TSPData.secondOrientations
      (data.weights.drop data.vertexCount))
  let leading := data.weights.take data.vertexCount
  let rest := data.weights.drop data.vertexCount
  have hsplit : leading ++ rest = data.weights := by
    exact List.take_append_drop _ _
  have hleading : leading.length = data.vertexCount := by
    simp [leading, vertexCount_le_weights_length data hshape]
  have hrest : rest.length =
      2 * (vertexCoverNormalizedPairs data.vertexCount).length := by
    have hpairs : tspNormalizedPairs data.vertexCount =
        vertexCoverNormalizedPairs data.vertexCount := by
      induction data.vertexCount with
      | zero => rfl
      | succ n ih =>
          simp only [tspNormalizedPairs, vertexCoverNormalizedPairs, ih]
    simpa [rest, hpairs] using tail_length data hshape
  rw [← hsplit, ← hleading]
  rw [select_false_prefix]
  simpa [hleading] using select_second_pairs _ rest hrest

/-- On structurally aligned canonical inputs, the concrete equality branch is
exactly the symmetric-matrix condition in `TSPData.WellFormed`. -/
theorem symmetryCheck_encode_iff (vertices : List Nat) (data : TSPData)
    (hcount : vertices.length = data.vertexCount)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    symmetryCheck (UnaryCertificate.encode vertices, encodeTSPData data) = true ↔
      TSPData.OrientationPairsEqual
        (data.weights.drop data.vertexCount) := by
  rw [symmetryCheck, decide_eq_true_eq,
    firstFields_encode vertices data hcount hshape,
    secondFields_encode vertices data hcount hshape,
    fieldBits_injective.eq_iff]
  exact (TSPData.orientationPairsEqual_iff _).symm

end CLRS.Chapter34.Turing.TSPVerifier.SymmetryCheck
