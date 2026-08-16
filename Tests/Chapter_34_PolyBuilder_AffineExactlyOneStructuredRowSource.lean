import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowSource

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

#check affineExactlyOneStructuredRowRevProgram
#check affineExactlyOneStructuredRowFrames
#check affineExactlyOneStructuredRow_runToFinish

example (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts))
      (affineExactlyOneStructuredRowLoadedCfg labelWidth stateWidth cellCounts
        height start rowBase input output)
      (some (affineExactlyOneStructuredRowFinishCfg labelWidth stateWidth
        cellCounts height start rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowFrames labelWidth stateWidth
            cellCounts height start rowBase)).reverse ++ output)))
      (affineExactlyOneStructuredRowSteps labelWidth stateWidth cellCounts
        height start rowBase) :=
  affineExactlyOneStructuredRow_runToFinish labelWidth stateWidth cellCounts
    height start rowBase input output

#print axioms affineExactlyOneStructuredRow_runToFinish

end CLRS.Chapter34.Turing.PolyBuilder
