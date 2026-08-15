import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check CircuitBuilder.disjunctionGateTrace
#check CircuitBuilder.disjunction_gates_eq
#check CircuitBuilder.disjunction_wire_eq_trace
#check AffineOrFinPairFrame
#check encodeAffineOrFinFrames
#check affineOrFinCanonicalFrames
#check affineOrFinCanonicalGateStream_eq_trace
#check affineOrFin_runToFinish
#check affineOrFinCanonical_run
#check affineOrFinRev_steps_le

example : affineOrFinCanonicalFrames 10 [2, 4, 9] =
    [{ left := 9, right := 10 },
     { left := 4, right := 11 },
     { left := 2, right := 12 }] := by
  native_decide

example : affineOrFinGateStream
      (affineOrFinCanonicalFrames 10 [2, 4, 9]) =
    (CircuitBuilder.disjunctionGateTrace 10 [2, 4, 9]).gates.flatMap
      encodeCircuitGate := by
  exact affineOrFinCanonicalGateStream_eq_trace 10 [2, 4, 9]

example : affineOrFinRevSteps
      (affineOrFinCanonicalFrames 10 [2, 4, 9]) ≤
    100 * (encodeAffineOrFinFrames
      (affineOrFinCanonicalFrames 10 [2, 4, 9])).length + 3 := by
  exact affineOrFinRev_steps_le _

#print axioms CircuitBuilder.disjunction_gates_eq
#print axioms affineOrFinCanonicalGateStream_eq_trace
#print axioms affineOrFin_runToFinish
#print axioms affineOrFinCanonical_run
#print axioms affineOrFinRev_steps_le
