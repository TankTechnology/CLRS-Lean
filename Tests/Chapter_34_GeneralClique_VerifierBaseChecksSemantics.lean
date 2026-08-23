import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Semantics

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier

#check BaseChecks.baseChecks_encode_iff
#check BaseChecks.baseConditions_complete_iff

example (I : CliqueInstance) (vertices : List Nat) :
    BaseChecks.baseChecks (encodeCliqueCertificate vertices)
        (encodeCliqueInstance I) = true ↔
      BaseChecks.BaseConditions I vertices :=
  BaseChecks.baseChecks_encode_iff I vertices
