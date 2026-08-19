import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NotFamily

open StateTransition
open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check encodeAffineNotFamilySources
#check affineNotFamilyGateStream
#check affineNotFamilyGateStream_eq_trace
#check affineNotFamily_run
#check affineNotFamily_runToFinishWithTail
#check affineNotFamilyRev_steps_le

example : affineNotFamilyGateStream [2, 5] =
    ([CircuitGate.not 2, CircuitGate.not 5]).flatMap encodeCircuitGate := by
  exact affineNotFamilyGateStream_eq_trace [2, 5]

example (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg (encodeAffineNotFamilySources [2, 5]) output)
      (some (haltCfg affineNotFamilyRevProgram
        ((affineNotFamilyGateStream [2, 5]).reverse ++ output)))
      (affineNotFamilyRevSteps [2, 5]) := by
  exact affineNotFamily_run [2, 5] output

#print axioms affineNotFamilyGateStream_eq_trace
#print axioms affineNotFamily_run
#print axioms affineNotFamily_runToFinishWithTail
#print axioms affineNotFamilyRev_steps_le
