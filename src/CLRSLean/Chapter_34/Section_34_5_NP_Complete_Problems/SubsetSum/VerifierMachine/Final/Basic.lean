import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.SumCheck
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

/-! # Complete fixed polynomial-time SUBSET-SUM verifier -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.Final

open _root_.Turing

abbrev RawInput := MaskFlags.RawInput

def rawEncoding : RawInput → List (Option SubsetSumSym) :=
  MaskFlags.rawEncoding

def concreteSubsetSumVerifier (input : RawInput) : Bool :=
  Syntax.instanceSyntax input.2 &&
    (Syntax.maskSyntax input.1 && SumCheck.sumCheck input)

private noncomputable def instanceSyntaxComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => Syntax.instanceSyntax input.2) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TSPVerifier.StructuralChecks.instanceProjection
    Syntax.instanceComputableInPolyTime
  change TM2ComputableInPolyTime TSPVerifier.StructuralChecks.rawEncoding
    TM2Comp.boolEncoding (fun input => Syntax.instanceSyntax input.2)
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def maskSyntaxComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => Syntax.maskSyntax input.1) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TSPVerifier.StructuralChecks.certificateProjection
    Syntax.maskComputableInPolyTime
  change TM2ComputableInPolyTime TSPVerifier.StructuralChecks.rawEncoding
    TM2Comp.boolEncoding (fun input => Syntax.maskSyntax input.1)
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def certificateAndSumComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => Syntax.maskSyntax input.1 && SumCheck.sumCheck input) := by
  exact TM2AndOr.andOrComputableInPolyTime
    maskSyntaxComputableInPolyTime SumCheck.sumCheckComputableInPolyTime Bool.and

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      concreteSubsetSumVerifier := by
  exact TM2AndOr.andOrComputableInPolyTime
    instanceSyntaxComputableInPolyTime
    certificateAndSumComputableInPolyTime Bool.and

end CLRS.Chapter34.Turing.SubsetSumVerifier.Final
