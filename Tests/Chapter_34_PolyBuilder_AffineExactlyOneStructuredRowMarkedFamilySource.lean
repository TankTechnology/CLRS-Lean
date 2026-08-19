import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource

open StateTransition

open CLRS.Chapter34.Turing.PolyBuilder

#check encodeAffineExactlyOneStructuredRowMarkedFamily
#check affineExactlyOneStructuredRowMarkedFamilyRevProgram
#check affineExactlyOneStructuredRowMarkedFamilyRev_run
#check affineExactlyOneStructuredRowMarkedFamilyRev_computableInPolyTime
#check affineExactlyOneStructuredRowMarkedFamily_computableInPolyTime

example (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed)
    (rest : List AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneStructuredRowMarkedFamily
        labelWidth stateWidth cellCounts (seed :: rest) =
      encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowFrames labelWidth stateWidth
            cellCounts seed.height seed.start seed.rowBase) ++
        [.frameEnd] ++
        encodeAffineExactlyOneStructuredRowMarkedFamily
          labelWidth stateWidth cellCounts rest := rfl

#print axioms affineExactlyOneStructuredRowMarkedFamilyRev_run
#print axioms affineExactlyOneStructuredRowMarkedFamily_computableInPolyTime
