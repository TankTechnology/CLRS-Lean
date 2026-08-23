import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.VertexChecks

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

private def triangle : CliqueInstance :=
  { vertexCount := 3
    targetSize := 3
    edges := [(0, 1), (0, 2), (1, 2)] }

example : vertexChecks triangle [0, 1, 2] = true := by native_decide
example : vertexChecks triangle [0, 1, 1] = false := by native_decide
example : vertexChecks triangle [0, 1] = false := by native_decide
example : vertexChecks triangle [0, 1, 3] = false := by native_decide

#check natListNodupBool_eq_true_iff
#check verticesWithinBool_eq_true_iff
#check vertexChecks_eq_true_iff

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
