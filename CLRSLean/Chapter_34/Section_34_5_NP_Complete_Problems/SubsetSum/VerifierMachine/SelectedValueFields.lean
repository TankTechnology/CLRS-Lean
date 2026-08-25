import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.ValueBitFields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SelectDelimitedFields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-! # Fixed selection of the SUBSET-SUM value fields marked by a certificate -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.SelectedValueFields

open _root_.Turing
open PolyBuilder

abbrev RawInput := MaskFlags.RawInput

def rawEncoding : RawInput → List (Option SubsetSumSym) :=
  MaskFlags.rawEncoding

def filterInput (input : RawInput) :
    List Bool × List (Option Bool) :=
  (MaskFlags.flags input, ValueBitFields.fields input.2)

def selectedFields (input : RawInput) : List (Option Bool) :=
  SelectDelimitedFields.selectFields (filterInput input).1
    (filterInput input).2

private def leftPart (input : RawInput) :
    List (Option SelectDelimitedFields.InputSym) :=
  (MaskFlags.flags input).map fun flag => some (.flag flag)

private def rightPart (input : RawInput) :
    List (Option SelectDelimitedFields.InputSym) :=
  none :: (ValueBitFields.fields input.2).map fun field => some (.field field)

private noncomputable def leftPartComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id leftPart := by
  let mapped := listMap_computableInPolyTime
    (fun flag : Bool => some (SelectDelimitedFields.InputSym.flag flag))
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    MaskFlags.flagsComputableInPolyTime mapped
  change TM2ComputableInPolyTime MaskFlags.rawEncoding id
    (fun input => (MaskFlags.flags input).map fun flag =>
      some (SelectDelimitedFields.InputSym.flag flag))
  simpa only [Function.comp_def] using Classical.choice composed

private def rightSpec : StatefulFlatMapSpec Bool (Option Bool)
    (Option SelectDelimitedFields.InputSym) where
  initial := false
  action started field :=
    if started then ([some (.field field)], true)
    else ([none, some (.field field)], true)
  finish started := if started then [] else [none]

private theorem rightStarted (fields : List (Option Bool)) :
    rewriteStatefulFlatMapFrom rightSpec true fields =
      fields.map fun field => some (.field field) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec] using congrArg
        (fun tail => some (SelectDelimitedFields.InputSym.field field) :: tail)
        ih

private theorem rightRewrite (fields : List (Option Bool)) :
    rewriteStatefulFlatMap rightSpec fields =
      none :: fields.map fun field => some (.field field) := by
  cases fields with
  | nil => rfl
  | cons field fields =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec] using congrArg
        (fun tail => none ::
          some (SelectDelimitedFields.InputSym.field field) :: tail)
        (rightStarted fields)

private noncomputable def rightFormatterComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun fields : List (Option Bool) =>
        none :: fields.map fun field =>
          some (SelectDelimitedFields.InputSym.field field)) := by
  have machine := statefulFlatMap_computableInPolyTime rightSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun fields => by
        have output := machine.outputsFun fields
        rw [rightRewrite] at output
        exact output }

private noncomputable def rightPartComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id rightPart := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    ValueBitFields.fieldsComputableInPolyTime
    rightFormatterComputableInPolyTime
  change TM2ComputableInPolyTime ValueBitFields.rawEncoding id
    (fun input => none :: (ValueBitFields.fields input.2).map fun field =>
      some (SelectDelimitedFields.InputSym.field field))
  simpa only [Function.comp_def] using Classical.choice composed

private def encodeInputSymbol :
    Option SelectDelimitedFields.InputSym → UnaryFrameSym × UnaryFrameSym
  | none => (.tick, .tick)
  | some (.flag false) => (.tick, .separator)
  | some (.flag true) => (.tick, .frameEnd)
  | some (.field none) => (.separator, .tick)
  | some (.field (some false)) => (.separator, .separator)
  | some (.field (some true)) => (.separator, .frameEnd)

private def decodeInputSymbol : UnaryFrameSym → UnaryFrameSym →
    Option SelectDelimitedFields.InputSym
  | .tick, .tick => none
  | .tick, .separator => some (.flag false)
  | .tick, .frameEnd => some (.flag true)
  | .separator, .tick => some (.field none)
  | .separator, .separator => some (.field (some false))
  | .separator, .frameEnd => some (.field (some true))
  | _, _ => none

private theorem decode_encodeInputSymbol
    (symbol : Option SelectDelimitedFields.InputSym) :
    decodeInputSymbol (encodeInputSymbol symbol).1
      (encodeInputSymbol symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol =>
      cases symbol with
      | flag flag => cases flag <;> rfl
      | field field =>
          cases field with
          | none => rfl
          | some bit => cases bit <;> rfl

noncomputable def filterInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      SelectDelimitedFields.inputEncoding filterInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeInputSymbol decodeInputSymbol decode_encodeInputSymbol
    leftPartComputableInPolyTime rightPartComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [filterInput, SelectDelimitedFields.inputEncoding, leftPart,
          rightPart, Function.comp_def] using output }

noncomputable def selectedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id selectedFields := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    filterInputComputableInPolyTime
    SelectDelimitedFields.computableInPolyTime
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => SelectDelimitedFields.selectFields
      (filterInput input).1 (filterInput input).2)
  simpa only [selectedFields, Function.comp_def] using Classical.choice composed

@[simp] theorem selectedFields_encode (mask : List Bool)
    (data : SubsetSumData) :
    selectedFields (encodeSubsetSumMask mask, encodeSubsetSumData data) =
      SelectDelimitedFields.selectFields mask
        (data.values.flatMap fun value =>
          (encodeBinaryNat value).map some ++ [none]) := by
  simp [selectedFields, filterInput, ValueBitFields.fieldBits]

end CLRS.Chapter34.Turing.SubsetSumVerifier.SelectedValueFields
