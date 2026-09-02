import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairChecks

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

private def triangle : CliqueInstance :=
  { vertexCount := 3
    targetSize := 3
    edges := [(0, 1), (0, 2), (1, 2)] }

private def path : CliqueInstance :=
  { vertexCount := 3
    targetSize := 3
    edges := [(0, 1), (1, 2)] }

private def repeatedEdge : CliqueInstance :=
  { vertexCount := 2
    targetSize := 2
    edges := [(0, 1), (0, 1)] }

example : instanceWellFormedBool triangle = true := by native_decide
example : instanceWellFormedBool repeatedEdge = true := by native_decide
example : edgeListNodupBool repeatedEdge.edges = false := by native_decide
example : pairwiseAdjacencyBool triangle [0, 1, 2] = true := by native_decide
example : pairwiseAdjacencyBool path [0, 1, 2] = false := by native_decide
example : adjacencyBool triangle 2 0 = true := by native_decide
example : adjacencyBool triangle 1 1 = false := by native_decide

#check instanceWellFormedBool_eq_true_iff
#check adjacencyBool_eq_true_iff
#check pairwiseAdjacencyBool_eq_true_iff
#check pairwise_adj_iff_all_distinct

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
