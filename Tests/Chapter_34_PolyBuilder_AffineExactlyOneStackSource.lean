import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowOneHotOperands

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

#check affineExactlyOneStackRevProgram
#check affineExactlyOneStackFrames
#check affineExactlyOneStack_runToFinish

example (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStackRevProgram cellCount))
      (affineExactlyOneStackLoadedCfg cellCount height start rowBase input output)
      (some (affineExactlyOneStackFinishCfg cellCount height start rowBase
        input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStackFrames cellCount height start rowBase)).reverse ++
          output)))
      (affineExactlyOneStackSteps cellCount height start rowBase) :=
  affineExactlyOneStack_runToFinish cellCount height start rowBase input output

#print axioms affineExactlyOneStack_runToFinish

end CLRS.Chapter34.Turing.PolyBuilder

namespace CLRS.Chapter34.Turing.CookLevin

#check affineExactlyOneStackFrames_eq_arithmeticStack
#print axioms affineExactlyOneStackFrames_eq_arithmeticStack

end CLRS.Chapter34.Turing.CookLevin
