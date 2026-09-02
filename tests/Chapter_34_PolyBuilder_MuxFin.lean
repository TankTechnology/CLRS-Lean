import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.MuxFin

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check AffineMuxFinPairFrame
#check encodeAffineMuxFinHeader
#check encodeAffineMuxFinPairFrame
#check encodeAffineMuxFinFrames
#check affineMuxFinGateStream
#check affineMuxFinRevProgram
#check affineMuxFinCanonicalFrames
#check affineMuxFinCanonicalGateStream_eq_trace
#check affineMuxFin_runToFinish
#check affineMuxFinCanonical_run
#check affineMuxFinRev_steps_le

private def whenTrue2 : Fin 2 → CircuitBuilder.Wire :=
  fun i => if i.val = 0 then 1 else 2

private def whenFalse2 : Fin 2 → CircuitBuilder.Wire :=
  fun i => if i.val = 0 then 3 else 4

example : affineMuxFinCanonicalFrames 10 7 2 whenTrue2 whenFalse2 =
    [{ whenTrue := 1, whenFalse := 3, selector := 7,
       selectorNot := 10, trueArm := 11, falseArm := 12 },
     { whenTrue := 2, whenFalse := 4, selector := 7,
       selectorNot := 10, trueArm := 14, falseArm := 15 }] := by
  native_decide

example : affineMuxFinGateStream 7
      (affineMuxFinCanonicalFrames 10 7 2 whenTrue2 whenFalse2) =
    (CircuitBuilder.muxFinGateTrace 10 7 whenTrue2 whenFalse2).flatMap
      encodeCircuitGate := by
  exact affineMuxFinCanonicalGateStream_eq_trace 10 7 whenTrue2 whenFalse2

example : affineMuxFinRevSteps 7
      (affineMuxFinCanonicalFrames 10 7 2 whenTrue2 whenFalse2) ≤
    200 * (encodeAffineMuxFinFrames 7
      (affineMuxFinCanonicalFrames 10 7 2 whenTrue2 whenFalse2)).length + 2 := by
  exact affineMuxFinRev_steps_le _ _

#print axioms affineNotRev_runToHaltLabel
#print axioms affineExactlyOneFamily_not_runToFinish
#print axioms affineExactlyOneFamily_or_runToFinish
#print axioms affineMuxFinCanonicalGateStream_eq_trace
#print axioms affineMuxFin_runToFinish
#print axioms affineMuxFinCanonical_run
#print axioms affineMuxFinRev_steps_le
