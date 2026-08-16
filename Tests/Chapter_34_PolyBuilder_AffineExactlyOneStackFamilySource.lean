import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackFamilySource

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

#check affineExactlyOneStackFamilyRevProgram
#check affineExactlyOneStackFamilyFrames
#check affineExactlyOneStackFamily_runToFinish

example (cellCounts : List Nat) (height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStackFamilyRevProgram cellCounts))
      (affineExactlyOneStackFamilyLoadedCfg cellCounts height start rowBase
        input output)
      (some (affineExactlyOneStackFamilyFinishCfg cellCounts height start
        rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStackFamilyFrames cellCounts height start rowBase)
          ).reverse ++ output)))
      (affineExactlyOneStackFamilySteps cellCounts height start rowBase) :=
  affineExactlyOneStackFamily_runToFinish cellCounts height start rowBase
    input output

#print axioms affineExactlyOneStackFamily_runToFinish

end CLRS.Chapter34.Turing.PolyBuilder
