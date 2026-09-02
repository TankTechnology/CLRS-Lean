import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.Semantics
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

/-!
# General CLIQUE verifier: final concrete machine

The total raw base checks and total raw adjacency pipeline are combined on
their shared separator encoding.  The resulting fixed machine computes the
previously published `cliqueVerifier` on every raw input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

open _root_.Turing

/-- Boolean function computed directly by the two concrete verifier branches. -/
def concreteCliqueVerifier (certificate input : List CliqueSym) : Bool :=
  BaseChecks.baseChecks certificate input &&
    AdjacencyPipeline.rawAdjacencyCheck (certificate, input)

private theorem baseChecks_decode_iff
    (certificate input : List CliqueSym) (I : CliqueInstance)
    (vertices : List Nat)
    (hcertificate : decodeCliqueCertificate certificate = some vertices)
    (hinput : decodeCliqueInstance input = some I) :
    BaseChecks.baseChecks certificate input = true ↔
      BaseChecks.BaseConditions I vertices := by
  have hcertificateCanonical :=
    encodeCliqueCertificate_eq_of_decode_eq_some
      certificate vertices hcertificate
  have hinputCanonical :=
    encodeCliqueInstance_eq_of_decode_eq_some input I hinput
  rw [← hcertificateCanonical, ← hinputCanonical]
  exact BaseChecks.baseChecks_encode_iff I vertices

/-- The final concrete Boolean is extensionally equal to the public verifier
on all raw certificate and input strings. -/
theorem concreteCliqueVerifier_eq_cliqueVerifier
    (certificate input : List CliqueSym) :
    concreteCliqueVerifier certificate input =
      cliqueVerifier certificate input := by
  apply Bool.eq_iff_iff.mpr
  rw [cliqueVerifier_eq_true_iff]
  constructor
  · intro hconcrete
    have hparts : BaseChecks.baseChecks certificate input = true ∧
        AdjacencyPipeline.rawAdjacencyCheck (certificate, input) = true := by
      simpa [concreteCliqueVerifier] using hconcrete
    rcases hparts with ⟨hbase, hadjacency⟩
    have hbaseParts : SyntaxPass.syntaxPass certificate input = true ∧
        BaseChecks.typedBaseChecks certificate input = true := by
      simpa [BaseChecks.baseChecks] using hbase
    have hsyntax := (SyntaxPass.syntaxPass_eq_true_iff certificate input).1
      hbaseParts.1
    rcases hsyntax with ⟨⟨vertices, hcertificate⟩, ⟨I, hinput⟩⟩
    have hconditions :=
      (baseChecks_decode_iff certificate input I vertices
        hcertificate hinput).1 hbase
    have hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2 := by
      intro edge hedge
      exact (hconditions.2.2.2 edge hedge).1
    have hpairs : pairwiseAdjacencyBool I vertices = true := by
      rw [← AdjacencyPipeline.rawAdjacencyCheck_eq_pairwise
        certificate input I vertices hcertificate hinput hstrict]
      exact hadjacency
    have hcomplete := (BaseChecks.baseConditions_complete_iff I vertices).1
      ⟨hconditions, (pairwiseAdjacencyBool_eq_true_iff I vertices).1 hpairs⟩
    exact ⟨I, vertices, hinput, hcertificate, hcomplete⟩
  · rintro ⟨I, vertices, hinput, hcertificate, hwellFormed, hclique⟩
    have hcomplete := (BaseChecks.baseConditions_complete_iff I vertices).2
      ⟨hwellFormed, hclique⟩
    have hbase := (baseChecks_decode_iff certificate input I vertices
      hcertificate hinput).2 hcomplete.1
    have hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2 := by
      intro edge hedge
      exact (hcomplete.1.2.2.2 edge hedge).1
    have hadjacency :
        AdjacencyPipeline.rawAdjacencyCheck (certificate, input) = true := by
      rw [AdjacencyPipeline.rawAdjacencyCheck_eq_pairwise
        certificate input I vertices hcertificate hinput hstrict]
      exact (pairwiseAdjacencyBool_eq_true_iff I vertices).2 hcomplete.2
    simpa [concreteCliqueVerifier] using And.intro hbase hadjacency

/-- A fixed polynomial-time TM2 computes the complete public CLIQUE verifier
on the original raw separator encoding. -/
noncomputable def cliqueVerifierComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun input : List CliqueSym × List CliqueSym =>
        pairEncoding input.1 input.2)
      TM2Comp.boolEncoding
      (fun input => cliqueVerifier input.1 input.2) := by
  let combined : TM2ComputableInPolyTime
      (fun input : List CliqueSym × List CliqueSym =>
        pairEncoding input.1 input.2)
      TM2Comp.boolEncoding
      (fun input => BaseChecks.baseChecks input.1 input.2 &&
        AdjacencyPipeline.rawAdjacencyCheck input) := by
    simpa using Turing.TM2AndOr.andOrComputableInPolyTime
      BaseChecks.baseChecksComputableInPolyTime
      AdjacencyPipeline.rawAdjacencyCheckComputableInPolyTime
      Bool.and
  exact
    { tm := combined.tm
      inputAlphabet := combined.inputAlphabet
      outputAlphabet := combined.outputAlphabet
      time := combined.time
      outputsFun := fun input => by
        have output := combined.outputsFun input
        have hsemantic : (BaseChecks.baseChecks input.1 input.2 &&
            AdjacencyPipeline.rawAdjacencyCheck input) =
              cliqueVerifier input.1 input.2 :=
          concreteCliqueVerifier_eq_cliqueVerifier input.1 input.2
        rw [hsemantic] at output
        simpa using output }

/-- Named polynomial runtime of the complete concrete CLIQUE verifier. -/
noncomputable def generalCliqueVerifierRuntimePolynomial : Polynomial Nat :=
  cliqueVerifierComputableInPolyTime.time

/-- The fixed compiled-and-composed verifier machine. -/
noncomputable def generalCliqueVerifierMachine : _root_.Turing.FinTM2 :=
  cliqueVerifierComputableInPolyTime.tm

/-- Exact-output and named-runtime contract for the fixed verifier machine on
every raw certificate/instance pair. -/
theorem generalCliqueVerifierMachine_outputs
    (input : List CliqueSym × List CliqueSym) :
    Nonempty (_root_.Turing.TM2OutputsInTime
      generalCliqueVerifierMachine
      (List.map cliqueVerifierComputableInPolyTime.inputAlphabet.invFun
        (pairEncoding input.1 input.2))
      (some (List.map
        cliqueVerifierComputableInPolyTime.outputAlphabet.invFun
        (TM2Comp.boolEncoding (cliqueVerifier input.1 input.2))))
      (generalCliqueVerifierRuntimePolynomial.eval
        (pairEncoding input.1 input.2).length)) := by
  exact ⟨cliqueVerifierComputableInPolyTime.outputsFun input⟩

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
