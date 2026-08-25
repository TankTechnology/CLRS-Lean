import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.SelectedValueFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SelectedWeightSum

/-! # Fixed binary sum of the SUBSET-SUM fields selected by the mask -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.SelectedSum

open _root_.Turing
open PolyBuilder

abbrev RawInput := MaskFlags.RawInput

def rawEncoding : RawInput → List (Option SubsetSumSym) :=
  MaskFlags.rawEncoding

def selectedSumBits (input : RawInput) : List Bool :=
  DelimitedBinarySum.sumDelimited (SelectedValueFields.selectedFields input)

noncomputable def selectedSumBitsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id selectedSumBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SelectedValueFields.selectedFieldsComputableInPolyTime
    DelimitedBinarySum.computableInPolyTime
  change TM2ComputableInPolyTime SelectedValueFields.rawEncoding id
    (fun input => DelimitedBinarySum.sumDelimited
      (SelectedValueFields.selectedFields input))
  simpa only [Function.comp_def] using Classical.choice composed

theorem binaryNatValue_selectedSumBits_encode (mask : List Bool)
    (data : SubsetSumData) :
    binaryNatValue
        (selectedSumBits
          (encodeSubsetSumMask mask, encodeSubsetSumData data)) =
      (subsetSumMaskValues mask data.values).sum := by
  rw [selectedSumBits, SelectedValueFields.selectedFields_encode]
  change binaryNatValue
      (DelimitedBinarySum.sumDelimited
        (SelectDelimitedFields.selectFields mask
          (TSPVerifier.SelectedWeightSum.fieldBits data.values))) = _
  rw [TSPVerifier.SelectedWeightSum.selectFields_fieldBits]
  exact DelimitedBinarySum.binaryNatValue_sumDelimited_encoded _

end CLRS.Chapter34.Turing.SubsetSumVerifier.SelectedSum
