import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.Semantics

/-!
# Regression test: total general CLIQUE adjacency pipeline
-/

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline

#check batchInputStreamComputableInPolyTime
#check rawAdjacencyCheckComputableInPolyTime
#check generatedCertificateQueries_eq_pairwise
#check rawAdjacencyCheck_eq_pairwise
