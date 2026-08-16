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
#print axioms affineCellProgressionSourceSteps_le

end CLRS.Chapter34.Turing.PolyBuilder
