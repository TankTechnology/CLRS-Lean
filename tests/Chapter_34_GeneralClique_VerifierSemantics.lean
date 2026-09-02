import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Semantics

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

private def triangle : CliqueInstance :=
  { vertexCount := 3
    targetSize := 3
    edges := [(0, 1), (0, 2), (1, 2)] }

example : typedCliqueChecks triangle [0, 1, 2] = true := by native_decide
example : factoredCliqueVerifier (encodeCliqueCertificate [0, 1, 2])
    (encodeCliqueInstance triangle) = true := by native_decide
example : factoredCliqueVerifier (encodeCliqueCertificate [0, 1, 1])
    (encodeCliqueInstance triangle) = false := by native_decide

#check typedCliqueChecks_eq_true_iff
#check typedCliqueChecks_eq_decide
#check factoredCliqueVerifier_eq_cliqueVerifier
#check factoredCliqueVerifier_eq_true_iff

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
