import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SelectedWeightFields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DelimitedBinarySum
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowSelection

/-! # Decision-TSP verifier: sum of selected weight fields -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.SelectedWeightSum

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

/-- Values retained by a pointwise Boolean selection stream.  The recursion
stops at the shorter input, matching the concrete delimited-field selector. -/
def selectedValues : List Bool → List Nat → List Nat
  := selectListByBool

/-- Compact binary representation of the total weight selected from the
physical matrix. -/
def selectedSumBits (input : RawInput) : List Bool :=
  DelimitedBinarySum.sumDelimited
    (SelectedWeightFields.selectedFields input)

/-- The complete selected-weight summation is performed by one fixed
polynomial-time machine. -/
noncomputable def selectedSumBitsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id selectedSumBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SelectedWeightFields.selectedFieldsComputableInPolyTime
    DelimitedBinarySum.computableInPolyTime
  change TM2ComputableInPolyTime SelectedWeightFields.rawEncoding id
    (fun input => DelimitedBinarySum.sumDelimited
      (SelectedWeightFields.selectedFields input))
  simpa only [Function.comp_def] using Classical.choice composed

def fieldBits (values : List Nat) : List (Option Bool) :=
  values.flatMap fun value => (encodeBinaryNat value).map some ++ [none]

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

/-- Semantic normal form of the reusable field selector on encoded natural
numbers. -/
theorem selectFields_fieldBits (flags : List Bool) (values : List Nat) :
    SelectDelimitedFields.selectFields flags (fieldBits values) =
      fieldBits (selectedValues flags values) := by
  induction flags generalizing values with
  | nil => simp [SelectDelimitedFields.selectFields, fieldBits, selectedValues,
      selectListByBool]
  | cons flag flags ih =>
      cases values with
      | nil => simp [SelectDelimitedFields.selectFields,
          SelectDelimitedFields.selectCurrent, fieldBits, selectedValues,
          selectListByBool]
      | cons value values =>
          simp only [fieldBits, List.flatMap_cons, List.append_assoc,
            List.singleton_append, SelectDelimitedFields.selectFields]
          rw [selectCurrent_field]
          have ih' := ih values
          change SelectDelimitedFields.selectFields flags
              (values.flatMap fun value =>
                (encodeBinaryNat value).map some ++ [none]) =
            (selectedValues flags values).flatMap fun value =>
              (encodeBinaryNat value).map some ++ [none] at ih'
          cases flag with
          | false => simpa [selectedValues, selectListByBool] using ih'
          | true =>
              rw [ih']
              simp [selectedValues, selectListByBool, List.append_assoc]

theorem binaryNatValue_selectedSumBits_encode
    (vertices : List Nat) (data : TSPData) :
    binaryNatValue
        (selectedSumBits
          (UnaryCertificate.encode vertices, encodeTSPData data)) =
      (selectedValues
        (List.replicate vertices.length false ++
          ((vertexCoverNormalizedPairs vertices.length).map fun edge =>
            decide (edge ∈
              (HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices).map
                GeneralCliqueVerifier.QueryNormalizer.normalizeQuery)).flatMap
                  fun flag => [flag, flag])
        data.weights).sum := by
  rw [selectedSumBits, SelectedWeightFields.selectedFields_encode]
  let flags := List.replicate vertices.length false ++
    ((vertexCoverNormalizedPairs vertices.length).map fun edge =>
      decide (edge ∈
        (HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices).map
          GeneralCliqueVerifier.QueryNormalizer.normalizeQuery)).flatMap
            fun flag => [flag, flag]
  change binaryNatValue
      (DelimitedBinarySum.sumDelimited
        (SelectDelimitedFields.selectFields flags (fieldBits data.weights))) =
    (selectedValues flags data.weights).sum
  rw [selectFields_fieldBits]
  exact DelimitedBinarySum.binaryNatValue_sumDelimited_encoded _

end CLRS.Chapter34.Turing.TSPVerifier.SelectedWeightSum
