import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.SelectedSum
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.HeaderBits

/-! # Compact target projection for the SUBSET-SUM verifier -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.TargetBits

open _root_.Turing

abbrev RawInput := MaskFlags.RawInput

def rawEncoding : RawInput → List (Option SubsetSumSym) :=
  MaskFlags.rawEncoding

def targetBits (input : RawInput) : List Bool :=
  TSPVerifier.HeaderBits.vertexCountBits input.2

@[simp] theorem targetBits_encode (mask : List Bool)
    (data : SubsetSumData) :
    targetBits (encodeSubsetSumMask mask, encodeSubsetSumData data) =
      encodeBinaryNat data.target := by
  rw [targetBits, TSPVerifier.HeaderBits.vertexCountBits,
    ValueBitFields.extract_encodeSubsetSumData]
  rw [show ValueBitFields.fieldBits (data.target :: data.values) =
    (encodeBinaryNat data.target).map some ++ none ::
      ValueBitFields.fieldBits data.values by
        simp [ValueBitFields.fieldBits, List.append_assoc]]
  exact TSPVerifier.HeaderBits.firstFieldBits_field _ _

noncomputable def targetBitsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id targetBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TSPVerifier.StructuralChecks.instanceProjection
    TSPVerifier.HeaderBits.vertexCountBitsComputableInPolyTime
  change TM2ComputableInPolyTime TSPVerifier.StructuralChecks.rawEncoding id
    (fun input => TSPVerifier.HeaderBits.vertexCountBits input.2)
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumVerifier.TargetBits
