import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

#check encodeAffineExactlyOneStructuredRowSeedMarkedFamily
#check affineExactlyOneStructuredRowSeedMarkedFamilyRevProgram
#check affineExactlyOneStructuredRowSeedMarkedFamilyRev_run
#check affineExactlyOneStructuredRowSeedMarkedFamilyRev_steps_le
#check affineExactlyOneStructuredRowSeedMarkedFamilyRev_computableInPolyTime
#check affineExactlyOneStructuredRowSeedMarkedFamily_computableInPolyTime

example (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed)
    (rest : List AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneStructuredRowSeedMarkedFamily
        labelWidth stateWidth cellCounts (seed :: rest) =
      encodeAffineExactlyOneStructuredRowSeed seed ++ [.frameEnd] ++
        encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowFrames labelWidth stateWidth
            cellCounts seed.height seed.start seed.rowBase) ++
        [.frameEnd] ++
        encodeAffineExactlyOneStructuredRowSeedMarkedFamily
          labelWidth stateWidth cellCounts rest := rfl

example (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime
      (step (affineExactlyOneStructuredRowSeedMarkedFamilyRevProgram
        labelWidth stateWidth cellCounts))
      (initialCfg
        (affineExactlyOneStructuredRowSeedMarkedFamilyRevProgram
          labelWidth stateWidth cellCounts)
        (encodeAffineExactlyOneStructuredRowSeedFamily seeds))
      (some (haltCfg
        (affineExactlyOneStructuredRowSeedMarkedFamilyRevProgram
          labelWidth stateWidth cellCounts)
        (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse))
      (affineExactlyOneStructuredRowSeedMarkedFamilyRevSteps
        labelWidth stateWidth cellCounts seeds) :=
  affineExactlyOneStructuredRowSeedMarkedFamilyRev_run
    labelWidth stateWidth cellCounts seeds

#print axioms affineExactlyOneStructuredRowSeedMarkedFamilyRev_run
#print axioms affineExactlyOneStructuredRowSeedMarkedFamilyRev_steps_le
#print axioms affineExactlyOneStructuredRowSeedMarkedFamily_computableInPolyTime

end CLRS.Chapter34.Turing.PolyBuilder
