import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.TargetBits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPairStream
import CLRSLean.Chapter_34.BinaryNat.Machine.Comparator
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

/-! # Exact selected-sum equality as two fixed binary comparisons -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.SumCheck

open _root_.Turing
open PolyBuilder

abbrev RawInput := MaskFlags.RawInput

def rawEncoding : RawInput → List (Option SubsetSumSym) :=
  MaskFlags.rawEncoding

def selectedLeTarget (input : RawInput) : Bool :=
  BinaryNat.Comparator.leWords (SelectedSum.selectedSumBits input)
    (TargetBits.targetBits input)

def targetLeSelected (input : RawInput) : Bool :=
  BinaryNat.Comparator.leWords (TargetBits.targetBits input)
    (SelectedSum.selectedSumBits input)

def sumCheck (input : RawInput) : Bool :=
  selectedLeTarget input && targetLeSelected input

private noncomputable def selectedLeTargetComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      selectedLeTarget := by
  let paired := BoolPairStream.computableInPolyTime
    SelectedSum.selectedSumBitsComputableInPolyTime
    TargetBits.targetBitsComputableInPolyTime
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    paired BinaryNat.Comparator.computableInPolyTime
  change TM2ComputableInPolyTime SelectedSum.rawEncoding
    TM2Comp.boolEncoding
    (fun input => BinaryNat.Comparator.leWords
      (SelectedSum.selectedSumBits input) (TargetBits.targetBits input))
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def targetLeSelectedComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      targetLeSelected := by
  let paired := BoolPairStream.computableInPolyTime
    TargetBits.targetBitsComputableInPolyTime
    SelectedSum.selectedSumBitsComputableInPolyTime
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    paired BinaryNat.Comparator.computableInPolyTime
  change TM2ComputableInPolyTime TargetBits.rawEncoding
    TM2Comp.boolEncoding
    (fun input => BinaryNat.Comparator.leWords
      (TargetBits.targetBits input) (SelectedSum.selectedSumBits input))
  simpa only [Function.comp_def] using Classical.choice composed

noncomputable def sumCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding sumCheck := by
  exact TM2AndOr.andOrComputableInPolyTime
    selectedLeTargetComputableInPolyTime
    targetLeSelectedComputableInPolyTime Bool.and

@[simp] theorem sumCheck_encode_iff (mask : List Bool)
    (data : SubsetSumData) :
    sumCheck (encodeSubsetSumMask mask, encodeSubsetSumData data) = true ↔
      data.MaskSumsTo mask := by
  simp only [sumCheck, Bool.and_eq_true,
    selectedLeTarget, targetLeSelected,
    BinaryNat.Comparator.leWords_eq_true_iff,
    SelectedSum.binaryNatValue_selectedSumBits_encode,
    TargetBits.targetBits_encode, binaryNatValue_encode,
    SubsetSumData.MaskSumsTo]
  omega

end CLRS.Chapter34.Turing.SubsetSumVerifier.SumCheck
