import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.VerifierTailController

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder
open StateTransition

#check AffineVerifierTailScript
#check encodeAffineVerifierTailScript
#check affineVerifierTailGateStream
#check affineVerifierTail_run
#check affineVerifierTailRev_steps_le

private def sample : AffineVerifierTailScript :=
  { initialFrames := []
    inputShape :=
      { separatorSources := [2]
        armFrames := [none]
        finalOrStart := 8
        finalOrWires := [] }
    acceptingFrames := none
    conjunctionFrame := { start := 10, wires := [3, 5] }
    outputWire := 12 }

example (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailLoopCfg (encodeAffineVerifierTailScript sample) output)
      (some (haltCfg affineVerifierTailRevProgram
        ((affineVerifierTailGateStream sample).reverse ++ output)))
      (affineVerifierTailRevSteps sample) := by
  exact affineVerifierTail_run sample output

#print axioms affineVerifierTail_run
#print axioms affineVerifierTailRev_steps_le
