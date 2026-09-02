import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.SyntaxSemantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.StructuralChecks

/-! # Boolean flag extraction from a SUBSET-SUM mask certificate -/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.MaskFlags

open _root_.Turing
open PolyBuilder

abbrev RawInput := List SubsetSumSym × List SubsetSumSym

def rawEncoding (input : RawInput) : List (Option SubsetSumSym) :=
  pairEncoding input.1 input.2

def extractSymbol : SubsetSumSym → List Bool
  | .bit flag => [flag]
  | _ => []

def extract (certificate : List SubsetSumSym) : List Bool :=
  certificate.flatMap extractSymbol

def flags (input : RawInput) : List Bool := extract input.1

private def spec : StatefulFlatMapSpec Unit SubsetSumSym Bool where
  initial := ()
  action _ symbol := (extractSymbol symbol, ())
  finish _ := []

private theorem rewriteFrom_eq (input : List SubsetSumSym) :
    rewriteStatefulFlatMapFrom spec () input = extract input := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec, extract] using congrArg (extractSymbol symbol ++ ·) ih

private theorem rewrite_eq (input : List SubsetSumSym) :
    rewriteStatefulFlatMap spec input = extract input := rewriteFrom_eq input

private theorem flatMap_bits (mask : List Bool) :
    (mask.map TSPSym.bit).flatMap extractSymbol = mask := by
  induction mask with
  | nil => rfl
  | cons flag mask ih => simp [extractSymbol, ih]

@[simp] theorem flags_encode (mask : List Bool) (data : SubsetSumData) :
    flags (encodeSubsetSumMask mask, encodeSubsetSumData data) = mask := by
  simp [flags, extract, encodeSubsetSumMask, extractSymbol, flatMap_bits]

private noncomputable def extractComputableInPolyTime :
    TM2ComputableInPolyTime id id extract := by
  have machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_eq] at output
        exact output }

noncomputable def flagsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id flags := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    TSPVerifier.StructuralChecks.certificateProjection
    extractComputableInPolyTime
  change TM2ComputableInPolyTime
    TSPVerifier.StructuralChecks.rawEncoding id (fun input => extract input.1)
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumVerifier.MaskFlags
