import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Canonical

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

private def triangle : CliqueInstance :=
  { vertexCount := 3
    targetSize := 3
    edges := [(0, 1), (0, 2), (1, 2)] }

example : cardinalityPass (encodeCliqueCertificate [0, 1, 2])
    (encodeCliqueInstance triangle) = true := by native_decide

example : cardinalityPass (encodeCliqueCertificate [0, 1])
    (encodeCliqueInstance triangle) = false := by native_decide

#check cardinality_run
#check cardinalitySteps_le
#check cardinalityPassComputableInPolyTime
#check cardinalityPass_encode_iff

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality
