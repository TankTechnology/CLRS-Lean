import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Runtime

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

#check rowRun
#check rowsRun
#check revRun
#check revSteps_le_input
#check rev_computableInPolyTime
#check rows_computableInPolyTime
#check entries_computableInPolyTime
#check pairIterations_computableInPolyTime

example : certificatePairEntries [2, 0, 3] =
    [(certificatePairOccurrence 0, 2),
      (certificatePairOccurrence 1, 0),
      (certificatePairOccurrence 2, 3)] := rfl

example : TMClique.encodeIndexedOccurrenceEntry
      (certificatePairOccurrence 2, 3) =
    PolyBuilder.encodeUnaryFrame [3, 2, 0, 1] ++
      [.frameEnd] := by
  exact encode_certificatePairEntry 2 3
