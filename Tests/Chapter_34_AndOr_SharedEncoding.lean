import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Runtime

/-!
# Regression test: Boolean composition over a shared nontrivial encoding

The general CLIQUE verifier components consume the same separator-based pair
encoding.  This test ensures that the reusable `TM2AndOr` construction composes
those concrete machines directly, without first changing their input domain to
raw identity-encoded words.
-/

noncomputable section

open CLRS Chapter34
open CLRS.Chapter34.Turing.GeneralCliqueVerifier
open Turing

noncomputable def syntaxAndCardinality :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      TM2Comp.boolEncoding
      (fun pr =>
        SyntaxPass.syntaxPass pr.1 pr.2 &&
          Cardinality.cardinalityPass pr.1 pr.2) :=
  TM2AndOr.andOrComputableInPolyTime
    SyntaxPass.syntaxPassComputableInPolyTime
    Cardinality.cardinalityPassComputableInPolyTime
    Bool.and

#check syntaxAndCardinality
