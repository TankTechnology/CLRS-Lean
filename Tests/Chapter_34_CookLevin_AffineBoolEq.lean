import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check affineBoolEqGateStream
#check affineBoolEqBodyCfg
#check affineBoolEqRevSteps
#check affineBoolEqRev_runFrom
#check affineBoolEqRev_steps_le

example : affineBoolEqRevSteps 5 2 4 = 286 := by native_decide

example : affineBoolEqGateStream 5 2 4 =
    (CircuitBuilder.boolEqGateTrace 5 2 4).gates.flatMap
      encodeCircuitGate := by
  exact affineBoolEqGateStream_eq_trace 5 2 4

#print axioms affineBoolEqGateStream_eq_trace
#print axioms affineBoolEqRev_runFrom
#print axioms affineBoolEqRev_steps_le
