import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.MaskFlags
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.FieldStream

/-!
# Delimited binary value fields for SUBSET-SUM

The shared compact-field extractor emits the target first.  A two-state
transducer discards that field and retains exactly the item-value fields.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.ValueBitFields

open _root_.Turing
open PolyBuilder

abbrev RawInput := MaskFlags.RawInput

def rawEncoding : RawInput → List (Option SubsetSumSym) :=
  MaskFlags.rawEncoding

inductive Mode | skipTarget | values
deriving DecidableEq, Fintype

private def spec : StatefulFlatMapSpec Mode (Option Bool) (Option Bool) where
  initial := .skipTarget
  action mode symbol :=
    match mode, symbol with
    | .skipTarget, some _ => ([], .skipTarget)
    | .skipTarget, none => ([], .values)
    | .values, field => ([field], .values)
  finish _ := []

def dropTarget (fields : List (Option Bool)) : List (Option Bool) :=
  rewriteStatefulFlatMap spec fields

def fields (input : List SubsetSumSym) : List (Option Bool) :=
  dropTarget (TSPVerifier.FieldStream.extract input)

private theorem valuesFrom (fields : List (Option Bool)) :
    rewriteStatefulFlatMapFrom spec .values fields = fields := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec] using congrArg (field :: ·) ih

private theorem dropTarget_field (bits : List Bool)
    (suffix : List (Option Bool)) :
    dropTarget (bits.map some ++ none :: suffix) = suffix := by
  unfold dropTarget rewriteStatefulFlatMap
  induction bits with
  | nil =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact valuesFrom suffix
  | cons bit bits ih =>
      rw [List.map_cons, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec] using ih

def fieldBits (values : List Nat) : List (Option Bool) :=
  values.flatMap fun value => (encodeBinaryNat value).map some ++ [none]

theorem extract_encodeSubsetSumData (data : SubsetSumData) :
    TSPVerifier.FieldStream.extract (encodeSubsetSumData data) =
      fieldBits (data.target :: data.values) := by
  rw [encodeSubsetSumData]
  simp only [TSPVerifier.FieldStream.extract, List.flatMap_cons,
    TSPVerifier.FieldStream.extractSymbol, List.nil_append,
    List.flatMap_append]
  rw [← TSPVerifier.FieldStream.extract,
    TSPVerifier.FieldStream.extract_encodeTSPFields]
  simp [fieldBits]

@[simp] theorem fields_encode (data : SubsetSumData) :
    fields (encodeSubsetSumData data) = fieldBits data.values := by
  rw [fields, extract_encodeSubsetSumData]
  rw [show fieldBits (data.target :: data.values) =
    (encodeBinaryNat data.target).map some ++ none ::
      fieldBits data.values by simp [fieldBits, List.append_assoc]]
  exact dropTarget_field _ _

private noncomputable def dropTargetComputableInPolyTime :
    TM2ComputableInPolyTime id id dropTarget :=
  statefulFlatMap_computableInPolyTime spec

noncomputable def fieldsFromInstanceComputableInPolyTime :
    TM2ComputableInPolyTime id id fields := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TSPVerifier.FieldStream.computableInPolyTime
    dropTargetComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => dropTarget (TSPVerifier.FieldStream.extract input))
  simpa only [Function.comp_def] using Classical.choice composed

noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id (fun input => fields input.2) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TSPVerifier.StructuralChecks.instanceProjection
    fieldsFromInstanceComputableInPolyTime
  change TM2ComputableInPolyTime TSPVerifier.StructuralChecks.rawEncoding id
    (fun input => fields input.2)
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumVerifier.ValueBitFields
