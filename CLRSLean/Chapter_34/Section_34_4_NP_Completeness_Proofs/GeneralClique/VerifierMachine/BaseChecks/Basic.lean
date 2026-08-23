import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Basic

/-!
# General CLIQUE verifier: already-compiled base checks

This module gives a stable Boolean interface to the six independent raw passes
whose concrete machines have already been verified.  Certificate pairwise
adjacency is intentionally not included here.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BaseChecks

/-- Cardinality and target-size bounds. -/
def cardinalityAndTarget (certificate input : List CliqueSym) : Bool :=
  Cardinality.cardinalityPass certificate input &&
    TargetBound.targetBoundPass certificate input

/-- All currently compiled certificate-side conditions. -/
def certificateChecks (certificate input : List CliqueSym) : Bool :=
  cardinalityAndTarget certificate input &&
    CertificateRange.certificateRangePass certificate input

/-- Both currently compiled per-edge well-formedness conditions. -/
def graphChecks (certificate input : List CliqueSym) : Bool :=
  EdgeOrder.edgeOrderPass certificate input &&
    EndpointBound.endpointBoundPass certificate input

/-- The non-syntax part of the already-compiled checks. -/
def typedBaseChecks (certificate input : List CliqueSym) : Bool :=
  certificateChecks certificate input && graphChecks certificate input

/-- Conjunction of all six raw passes with verified concrete machines. -/
def baseChecks (certificate input : List CliqueSym) : Bool :=
  SyntaxPass.syntaxPass certificate input &&
    typedBaseChecks certificate input

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BaseChecks
