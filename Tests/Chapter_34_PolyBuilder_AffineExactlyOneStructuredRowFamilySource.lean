import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

#check AffineExactlyOneStructuredRowSeed
#check encodeAffineExactlyOneStructuredRowSeedFamily
#check affineExactlyOneStructuredRowFamilyFrames
#check affineExactlyOneStructuredRowFamilyRevProgram
#check affineExactlyOneStructuredRowFamilyRev_run

example (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime
      (step (affineExactlyOneStructuredRowFamilyRevProgram
        labelWidth stateWidth cellCounts))
      (initialCfg
        (affineExactlyOneStructuredRowFamilyRevProgram
          labelWidth stateWidth cellCounts)
        (encodeAffineExactlyOneStructuredRowSeedFamily seeds))
      (some (haltCfg
        (affineExactlyOneStructuredRowFamilyRevProgram
          labelWidth stateWidth cellCounts)
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowFamilyFrames
            labelWidth stateWidth cellCounts seeds)).reverse)))
      (affineExactlyOneStructuredRowFamilyRevSteps
        labelWidth stateWidth cellCounts seeds) :=
  affineExactlyOneStructuredRowFamilyRev_run
    labelWidth stateWidth cellCounts seeds

#print axioms affineExactlyOneStructuredRowFamilyRev_run

end CLRS.Chapter34.Turing.PolyBuilder
