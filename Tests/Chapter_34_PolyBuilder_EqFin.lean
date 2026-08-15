import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.EqFin

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check AffineEqFinPairFrame
#check encodeAffineEqFinPairFrame
#check encodeAffineEqFinFrames
#check affineEqFinGateStream
#check affineEqFinRevProgram
#check affineEqFinCanonicalFrames
#check affineEqFinCanonicalGateStream_eq_trace
#check affineEqFin_runToFinish
#check affineEqFinCanonical_run
#check affineEqFinRev_steps_le

private def left2 : Fin 2 → CircuitBuilder.Wire :=
  fun i => if i.val = 0 then 1 else 2

private def right2 : Fin 2 → CircuitBuilder.Wire :=
  fun i => if i.val = 0 then 3 else 4

example : affineEqFinCanonicalFrames 10 2 left2 right2 =
    [{ eqStart := 11, left := 1, right := 3,
       matched := 15, previous := 10 },
     { eqStart := 17, left := 2, right := 4,
       matched := 21, previous := 16 }] := by
  native_decide

example : affineEqFinGateStream
      (affineEqFinCanonicalFrames 10 2 left2 right2) =
    (CircuitBuilder.eqFinGateTrace 10 left2 right2).gates.flatMap
      encodeCircuitGate := by
  exact affineEqFinCanonicalGateStream_eq_trace 10 left2 right2

example : affineEqFinRevSteps
      (affineEqFinCanonicalFrames 10 2 left2 right2) ≤
    113 * (encodeAffineEqFinFrames
      (affineEqFinCanonicalFrames 10 2 left2 right2)).length + 3 := by
  exact affineEqFinRev_steps_le _

#print axioms affineExactlyOneFamily_and_runToFinish
#print axioms affineEqFinCanonicalGateStream_eq_trace
#print axioms affineEqFin_runToFinish
#print axioms affineEqFinCanonical_run
#print axioms affineEqFinRev_steps_le

