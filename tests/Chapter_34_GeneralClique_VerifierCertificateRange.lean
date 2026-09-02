import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Canonical

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

#check verticesWithinBool_eq_true_iff
#check certificateRangePass_encode_iff
#check program

example :
    certificateRangePass (encodeCliqueCertificate [0, 2, 3])
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 3, edges := [] }) = true := by
  decide

example :
    certificateRangePass (encodeCliqueCertificate [0, 4])
      (encodeCliqueInstance
        { vertexCount := 4, targetSize := 2, edges := [] }) = false := by
  decide
