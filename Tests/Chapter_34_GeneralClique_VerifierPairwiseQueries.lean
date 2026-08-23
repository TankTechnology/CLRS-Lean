import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairwiseQueries

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier

#check normalizeCertificatePair_mem_eq_adjacencyBool
#check certificatePairsDistinctBool_eq_true_iff
#check pairwiseAdjacencyBool_eq_normalized_queries
#check normalizedCertificatePairs_length_le

example : normalizedCertificatePairs [3, 1, 2] = [(1, 3), (2, 3), (1, 2)] := by
  native_decide

example : certificatePairsDistinctBool [2, 1, 2] = false := by
  native_decide
