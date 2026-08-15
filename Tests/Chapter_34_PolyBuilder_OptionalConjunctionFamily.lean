import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionalConjunctionFamily

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder
open StateTransition

#check encodeAffineOptionalConjunctionFamily
#check affineOptionalConjunctionFamilyGateStream
#check affineOptionalConjunctionFamily_run
#check affineOptionalConjunctionFamilyRev_steps_le

private def sampleFrame : AffineConjunctionFrame :=
  { start := 7, wires := [1, 3] }

example : affineOptionalConjunctionFamilyGateStream
      [none, some sampleFrame, none] =
    affineConjunctionGateStream sampleFrame := by
  rfl

example (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily
          [none, some sampleFrame, none]) output)
      (some (haltCfg affineOptionalConjunctionFamilyRevProgram
        ((affineConjunctionGateStream sampleFrame).reverse ++ output)))
      (affineOptionalConjunctionFamilyRevSteps
        [none, some sampleFrame, none]) := by
  simpa [affineOptionalConjunctionFamilyGateStream,
    affineOptionalConjunctionEntryGateStream] using
      affineOptionalConjunctionFamily_run
        [none, some sampleFrame, none] output

#print axioms affineOptionalConjunctionFamily_run
#print axioms affineOptionalConjunctionFamilyRev_steps_le
