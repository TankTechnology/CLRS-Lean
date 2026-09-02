import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailRowFamilySource

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

#check affineCellProgressionFrames
#check affineCellProgressionFrames_succ
#check affineCellProgressionFrames_eq_ofFn
#check affineCellProgressionSourceRevProgram
#check affineCellProgressionSourceSteps_phase_le
#check affineCellProgressionSourceSteps_le
#check affineCellProgressionSource_runToFinish
#check affineCellProgressionSource_runToFinishWithTail
#check AffineRuntimeStackSourceSeed
#check affineRuntimeStackSourceFrame
#check affineRuntimeStackSourceRevProgram
#check affineRuntimeStackSource_runToFinish
#check affineRuntimeStackSource_runToFinishWithTail
#check affineRuntimeStackSourceSteps_le

example (blankStep count right left blank : Nat)
    (output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineCellProgressionSourceRevProgram blankStep))
      (affineCellProgressionSourceLoadedCfg blankStep count
        right left blank output)
      (some (affineCellProgressionSourceFinishCfg blankStep count
        right left blank
        ((encodeAffineCellFamily
          (affineCellProgressionFrames blankStep count
            right left blank)).reverse ++ output)))
      (affineCellProgressionSourceSteps blankStep count
        right left blank) :=
  affineCellProgressionSource_runToFinish
    blankStep count right left blank output

#print axioms affineCellProgressionSource_runToFinish
#print axioms affineCellProgressionSource_runToFinishWithTail
#print axioms affineCellProgressionSourceSteps_le
#print axioms affineRuntimeStackSource_runToFinish
#print axioms affineRuntimeStackSource_runToFinishWithTail
#print axioms affineRuntimeStackSourceSteps_le

end CLRS.Chapter34.Turing.PolyBuilder
