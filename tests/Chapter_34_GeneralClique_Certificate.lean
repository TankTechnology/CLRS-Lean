import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate

namespace CLRS.Chapter34

private def oneEdgeClique : CliqueInstance where
  vertexCount := 2
  targetSize := 2
  edges := [(0, 1)]

#check CliqueInstance.ListRepresentsClique
#check cliqueVerifier_eq_true_iff
#check mem_generalCLIQUE_iff_exists_certificate

example : cliqueVerifier (encodeCliqueCertificate [0, 1])
    (encodeCliqueInstance oneEdgeClique) = true := by native_decide

example : cliqueVerifier (encodeCliqueCertificate [0, 0])
    (encodeCliqueInstance oneEdgeClique) = false := by native_decide

example : cliqueVerifier [.certificateMark, .vertexMark]
    (encodeCliqueInstance oneEdgeClique) = false := by native_decide

example : cliqueVerifier (encodeCliqueCertificate [0, 1])
    [.certificateMark] = false := by native_decide

end CLRS.Chapter34
