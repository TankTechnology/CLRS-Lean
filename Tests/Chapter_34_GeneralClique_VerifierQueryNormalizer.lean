import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Composition

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

#check rowRun
#check rowsRun
#check revRun
#check rowSteps_le_encoding
#check rowsSteps_le_encoding
#check revSteps_le_input
#check rev_computableInPolyTime
#check queries_computableInPolyTime
#check normalizer_computableInPolyTime
#check PairGenerator.rawPairs_computableInPolyTime
#check normalizedCertificatePairs_computableInPolyTime

example : normalizeQuery (5, 2) = (2, 5) := by decide

example : normalizeQuery (3, 3) = (3, 3) := by decide

example : PairGenerator.certificateRawPairs [2, 0, 3] =
    [(2, 0), (2, 3), (0, 3)] := by decide

example : normalizedCertificatePairs [2, 0, 3] =
    [(0, 2), (2, 3), (0, 3)] := by decide

/-- Equal certificate values deliberately survive as a loop query; canonical
simple-graph lookup will reject that query because canonical instances have
no loop records. -/
example : normalizedCertificatePairs [2, 2] = [(2, 2)] := by decide
