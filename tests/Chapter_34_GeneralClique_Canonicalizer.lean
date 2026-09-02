import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Runtime

/-!
# Regression test: total raw CLIQUE canonicalization
-/

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

#check certificateSyntaxAccepts_eq_true_iff
#check instanceSyntaxAccepts_eq_true_iff
#check canonicalStream_certificate_eq
#check canonicalStream_instance_eq
#check certificateComputableInPolyTime
#check instanceComputableInPolyTime

example : certificateValue [] = [] := rfl

example : instanceValue [] = emptyInstance := rfl

example : canonicalStream .certificate [] = encodeCliqueCertificate [] := by
  exact canonicalStream_certificate_eq []

example : canonicalStream .instance [] = encodeCliqueInstance emptyInstance := by
  exact canonicalStream_instance_eq []
