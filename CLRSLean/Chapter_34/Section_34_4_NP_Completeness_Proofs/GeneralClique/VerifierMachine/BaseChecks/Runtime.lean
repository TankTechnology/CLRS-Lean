import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Runtime

/-!
# General CLIQUE verifier: concrete base-check machine

The reusable same-input Boolean composition construction joins the six fixed
component machines while preserving their common separator-based pair
encoding and an explicit polynomial running-time witness.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BaseChecks

open _root_.Turing

private abbrev pairedEncoding :
    List CliqueSym × List CliqueSym → List (Option CliqueSym) :=
  fun pr => pairEncoding pr.1 pr.2

noncomputable def cardinalityAndTargetComputableInPolyTime :
    TM2ComputableInPolyTime pairedEncoding TM2Comp.boolEncoding
      (fun pr => cardinalityAndTarget pr.1 pr.2) := by
  simpa [pairedEncoding, cardinalityAndTarget] using
    TM2AndOr.andOrComputableInPolyTime
      Cardinality.cardinalityPassComputableInPolyTime
      TargetBound.targetBoundPassComputableInPolyTime
      Bool.and

noncomputable def certificateChecksComputableInPolyTime :
    TM2ComputableInPolyTime pairedEncoding TM2Comp.boolEncoding
      (fun pr => certificateChecks pr.1 pr.2) := by
  simpa [pairedEncoding, certificateChecks] using
    TM2AndOr.andOrComputableInPolyTime
      cardinalityAndTargetComputableInPolyTime
      CertificateRange.certificateRangePassComputableInPolyTime
      Bool.and

noncomputable def graphChecksComputableInPolyTime :
    TM2ComputableInPolyTime pairedEncoding TM2Comp.boolEncoding
      (fun pr => graphChecks pr.1 pr.2) := by
  simpa [pairedEncoding, graphChecks] using
    TM2AndOr.andOrComputableInPolyTime
      EdgeOrder.edgeOrderPassComputableInPolyTime
      EndpointBound.endpointBoundPassComputableInPolyTime
      Bool.and

noncomputable def typedBaseChecksComputableInPolyTime :
    TM2ComputableInPolyTime pairedEncoding TM2Comp.boolEncoding
      (fun pr => typedBaseChecks pr.1 pr.2) := by
  simpa [pairedEncoding, typedBaseChecks] using
    TM2AndOr.andOrComputableInPolyTime
      certificateChecksComputableInPolyTime
      graphChecksComputableInPolyTime
      Bool.and

/-- A fixed TM2 computes the conjunction of all six completed passes in
polynomial time on the original raw certificate/instance pair encoding. -/
noncomputable def baseChecksComputableInPolyTime :
    TM2ComputableInPolyTime pairedEncoding TM2Comp.boolEncoding
      (fun pr => baseChecks pr.1 pr.2) := by
  simpa [pairedEncoding, baseChecks] using
    TM2AndOr.andOrComputableInPolyTime
      SyntaxPass.syntaxPassComputableInPolyTime
      typedBaseChecksComputableInPolyTime
      Bool.and

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BaseChecks
