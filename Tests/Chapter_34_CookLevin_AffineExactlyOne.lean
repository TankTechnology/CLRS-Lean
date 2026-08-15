import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder

#check affineSequentialExactlyOneGateStream
#check affineSequentialExactlyOneGateStream_eq_trace
#check affineSequentialExactlyOneGateList_eq_trace
#check affineSequentialExactlyOneBodyCfg
#check affineSequentialExactlyOneRevSteps
#check affineSequentialExactlyOneRev_runFrom
#check affineSequentialExactlyOneRev_steps_le

#print axioms affineSequentialExactlyOneGateList_eq_trace
#print axioms affineSequentialExactlyOneRev_runFrom
#print axioms affineSequentialExactlyOneRev_steps_le

example :
    AffineExactlyOne.gateList 5 7 0 =
      [.const false, .const false, .not 6, .and 5 7] := by
  native_decide

example :
    AffineExactlyOne.gateList 5 7 2 =
      (CookLevin.exactlyOneGateTrace 5 [7, 8]).gates := by
  native_decide

example : affineSequentialExactlyOneRevSteps 5 7 2 ≤
    200 * (5 + 7 + 2 + 1) ^ 2 := by
  exact affineSequentialExactlyOneRev_steps_le 5 7 2
