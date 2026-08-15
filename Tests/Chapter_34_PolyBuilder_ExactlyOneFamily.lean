import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder

#check AffineExactlyOneFrame
#check encodeAffineExactlyOneFrame
#check encodeAffineExactlyOneFamily
#check affineExactlyOneFamilyGateStream
#check affineExactlyOneFamilyRevProgram
#check affineExactlyOneFamilyLoopCfg
#check affineExactlyOneFamilyRevSteps
#check affineExactlyOneFamily_runOne
#check affineExactlyOneFamily_runToFinish
#check affineExactlyOneFamily_run
#check affineExactlyOneFamilyRev_steps_le
#check affineExactlyOneFamilyUntilEnd_steps_le

#print axioms affineExactlyOneFamilyGateStream_eq_flatMap
#print axioms affineExactlyOneFamily_runToFinish
#print axioms affineExactlyOneFamily_run
#print axioms affineExactlyOneFamilyRev_steps_le
#print axioms affineExactlyOneFamilyUntilEnd_steps_le

private def sampleFrames : List AffineExactlyOneFrame :=
  [{ start := 5, rowBase := 7, count := 2 },
   { start := 15, rowBase := 20, count := 1 }]

example : affineExactlyOneFamilyGateStream sampleFrames =
    affineSequentialExactlyOneGateStream 5 7 2 ++
      affineSequentialExactlyOneGateStream 15 20 1 := by
  native_decide

example : affineExactlyOneFamilyRevSteps sampleFrames ≤
    400 * (encodeAffineExactlyOneFamily sampleFrames).length ^ 2 + 2 := by
  exact affineExactlyOneFamilyRev_steps_le sampleFrames
