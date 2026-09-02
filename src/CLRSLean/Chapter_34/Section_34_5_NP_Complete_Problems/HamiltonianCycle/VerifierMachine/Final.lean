import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Certificate.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CertificateNodup
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.ComponentChecks
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CycleAdjacency
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Semantics
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr
import Mathlib.Tactic

/-!
# HAM-CYCLE verifier: final fixed machine

The final Boolean combines five independently verified branches over the
same raw separator encoding:

1. the reusable CLIQUE syntax, cardinality, range, and graph checks;
2. target equality;
3. the minimum three-vertex side condition;
4. certificate distinctness;
5. all consecutive and closing cycle-edge queries.

The semantic theorem below identifies this concrete conjunction with the
public `hamiltonianCycleVerifier` on every raw input, including malformed
strings.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine

open _root_.Turing

/-- Repackage a concrete machine along a pointwise-identical input encoding.
This is needed because the reusable verifier components give the same
separator encoding different module-local names. -/
private noncomputable def reencodeInput
    {α β αΓ βΓ : Type} {sourceEncoding targetEncoding : α → List αΓ}
    {outputEncoding : β → List βΓ} {f : α → β}
    (source : TM2ComputableInPolyTime sourceEncoding outputEncoding f)
    (hencoding : ∀ input, sourceEncoding input = targetEncoding input) :
    TM2ComputableInPolyTime targetEncoding outputEncoding f :=
  { tm := source.tm
    inputAlphabet := source.inputAlphabet
    outputAlphabet := source.outputAlphabet
    time := source.time
    outputsFun := fun input => by
      rw [← hencoding input]
      exact source.outputsFun input }

/-- The two scalar graph-size conditions. -/
def scalarChecks (input : RawInput) : Bool :=
  targetEqualityCheck input && minimumVertexCountCheck input

/-- Certificate-local conditions beyond cardinality and range. -/
def cycleCertificateChecks (input : RawInput) : Bool :=
  CertificateNodup.nodupCheck input &&
    CycleAdjacency.rawCycleAdjacencyCheck input

/-- All HAM-specific checks. -/
def hamiltonianChecks (input : RawInput) : Bool :=
  scalarChecks input && cycleCertificateChecks input

/-- Complete concrete raw HAM-CYCLE verifier Boolean. -/
def concreteHamiltonianCycleVerifier (input : RawInput) : Bool :=
  GeneralCliqueVerifier.BaseChecks.baseChecks input.1 input.2 &&
    hamiltonianChecks input

private theorem baseChecks_decode_iff
    (certificate input : List CliqueSym) (I : CliqueInstance)
    (vertices : List Nat)
    (hcertificate : decodeCliqueCertificate certificate = some vertices)
    (hinput : decodeCliqueInstance input = some I) :
    GeneralCliqueVerifier.BaseChecks.baseChecks certificate input = true ↔
      GeneralCliqueVerifier.BaseChecks.BaseConditions I vertices := by
  have hcertificateCanonical :=
    encodeCliqueCertificate_eq_of_decode_eq_some
      certificate vertices hcertificate
  have hinputCanonical :=
    encodeCliqueInstance_eq_of_decode_eq_some input I hinput
  rw [← hcertificateCanonical, ← hinputCanonical]
  exact GeneralCliqueVerifier.BaseChecks.baseChecks_encode_iff I vertices

private theorem targetEqualityCheck_decode_iff
    (certificate input : List CliqueSym) (I : CliqueInstance)
    (hinput : decodeCliqueInstance input = some I) :
    targetEqualityCheck (certificate, input) = true ↔
      ¬I.targetSize < I.vertexCount := by
  have hinputCanonical :=
    encodeCliqueInstance_eq_of_decode_eq_some input I hinput
  rw [← hinputCanonical]
  exact targetEqualityCheck_encode_iff certificate I

private theorem minimumVertexCountCheck_decode_iff
    (certificate input : List CliqueSym) (I : CliqueInstance)
    (hinput : decodeCliqueInstance input = some I) :
    minimumVertexCountCheck (certificate, input) = true ↔
      3 ≤ I.vertexCount := by
  have hinputCanonical :=
    encodeCliqueInstance_eq_of_decode_eq_some input I hinput
  rw [← hinputCanonical]
  exact minimumVertexCountCheck_encode_iff certificate I

/-- The concrete conjunction is extensionally equal to the public verifier
on all raw certificate and graph words. -/
theorem concreteHamiltonianCycleVerifier_eq_public
    (certificate input : List CliqueSym) :
    concreteHamiltonianCycleVerifier (certificate, input) =
      hamiltonianCycleVerifier certificate input := by
  apply Bool.eq_iff_iff.mpr
  rw [hamiltonianCycleVerifier_eq_true_iff]
  constructor
  · intro hconcrete
    have hparts :
        GeneralCliqueVerifier.BaseChecks.baseChecks certificate input = true ∧
          ((targetEqualityCheck (certificate, input) = true ∧
              minimumVertexCountCheck (certificate, input) = true) ∧
            (CertificateNodup.nodupCheck (certificate, input) = true ∧
              CycleAdjacency.rawCycleAdjacencyCheck
                (certificate, input) = true)) := by
      simpa [concreteHamiltonianCycleVerifier, hamiltonianChecks,
        scalarChecks, cycleCertificateChecks] using hconcrete
    rcases hparts with
      ⟨hbase, ⟨⟨htarget, hminimum⟩, ⟨hnodup, hadjacency⟩⟩⟩
    have hbaseParts :
        GeneralCliqueVerifier.SyntaxPass.syntaxPass certificate input = true ∧
          GeneralCliqueVerifier.BaseChecks.typedBaseChecks
            certificate input = true := by
      simpa [GeneralCliqueVerifier.BaseChecks.baseChecks] using hbase
    have hsyntax :=
      (GeneralCliqueVerifier.SyntaxPass.syntaxPass_eq_true_iff
        certificate input).1 hbaseParts.1
    rcases hsyntax with ⟨⟨vertices, hcertificate⟩, ⟨I, hinput⟩⟩
    have hconditions :=
      (baseChecks_decode_iff certificate input I vertices
        hcertificate hinput).1 hbase
    rcases hconditions with
      ⟨hlengthTarget, htargetLe, hrange, hedges⟩
    have hnotlt :=
      (targetEqualityCheck_decode_iff certificate input I hinput).1 htarget
    have htargetEq : I.targetSize = I.vertexCount := by
      omega
    have hminimum' :=
      (minimumVertexCountCheck_decode_iff certificate input I hinput).1
        hminimum
    have hnodup' :=
      (CertificateNodup.nodupCheck_eq_true_iff certificate input vertices
        hcertificate).1 hnodup
    have hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2 := by
      intro edge hedge
      exact (hedges edge hedge).1
    have hnonempty : vertices ≠ [] := by
      intro hempty
      subst vertices
      simp only [List.length_nil] at hlengthTarget
      omega
    have hadjacency' : I.CycleAdjacent vertices := by
      have hdecide : decide (I.CycleAdjacent vertices) = true := by
        rw [← CycleAdjacency.rawCycleAdjacencyCheck_eq_cycleAdjacent
          certificate input I vertices hcertificate hinput hstrict hnonempty]
        exact hadjacency
      exact of_decide_eq_true hdecide
    have hwellFormed : I.WellFormed :=
      ⟨htargetLe, hedges⟩
    have hlength : vertices.length = I.vertexCount := by
      omega
    have hcycle : I.ListRepresentsHamiltonianCycle vertices :=
      ⟨hminimum', hnodup', hlength, hrange, hadjacency'⟩
    exact ⟨I, vertices, hinput, hcertificate, hwellFormed,
      htargetEq, hcycle⟩
  · rintro ⟨I, vertices, hinput, hcertificate, hwellFormed,
      htargetEq, hcycle⟩
    rcases hwellFormed with ⟨htargetLe, hedges⟩
    rcases hcycle with
      ⟨hminimum', hnodup', hlength, hrange, hadjacency'⟩
    have hconditions :
        GeneralCliqueVerifier.BaseChecks.BaseConditions I vertices := by
      refine ⟨?_, htargetLe, hrange, hedges⟩
      omega
    have hbase :=
      (baseChecks_decode_iff certificate input I vertices
        hcertificate hinput).2 hconditions
    have htarget : targetEqualityCheck (certificate, input) = true :=
      (targetEqualityCheck_decode_iff certificate input I hinput).2 (by
        omega)
    have hminimum : minimumVertexCountCheck (certificate, input) = true :=
      (minimumVertexCountCheck_decode_iff certificate input I hinput).2
        hminimum'
    have hnodup : CertificateNodup.nodupCheck (certificate, input) = true :=
      (CertificateNodup.nodupCheck_eq_true_iff certificate input vertices
        hcertificate).2 hnodup'
    have hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2 := by
      intro edge hedge
      exact (hedges edge hedge).1
    have hnonempty : vertices ≠ [] := by
      intro hempty
      subst vertices
      simp only [List.length_nil] at hlength
      omega
    have hadjacency :
        CycleAdjacency.rawCycleAdjacencyCheck (certificate, input) = true := by
      rw [CycleAdjacency.rawCycleAdjacencyCheck_eq_cycleAdjacent
        certificate input I vertices hcertificate hinput hstrict hnonempty]
      exact decide_eq_true hadjacency'
    simpa [concreteHamiltonianCycleVerifier, hamiltonianChecks,
      scalarChecks, cycleCertificateChecks] using
        And.intro hbase
          (And.intro (And.intro htarget hminimum)
            (And.intro hnodup hadjacency))

/-- Fixed polynomial-time machine for the scalar checks. -/
noncomputable def scalarChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding scalarChecks := by
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => targetEqualityCheck input && minimumVertexCountCheck input)
  exact TM2AndOr.andOrComputableInPolyTime
    targetEqualityCheckComputableInPolyTime
    minimumVertexCountCheckComputableInPolyTime Bool.and

/-- Fixed polynomial-time machine for certificate distinctness and cycle
adjacency. -/
noncomputable def cycleCertificateChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      cycleCertificateChecks := by
  let nodup : TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      CertificateNodup.nodupCheck :=
    reencodeInput CertificateNodup.nodupCheckComputableInPolyTime (by
      intro input
      rfl)
  let adjacency : TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      CycleAdjacency.rawCycleAdjacencyCheck :=
    reencodeInput CycleAdjacency.computableInPolyTime (by
      intro input
      rfl)
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => CertificateNodup.nodupCheck input &&
      CycleAdjacency.rawCycleAdjacencyCheck input)
  exact TM2AndOr.andOrComputableInPolyTime nodup adjacency Bool.and

/-- Fixed polynomial-time machine for all HAM-specific branches. -/
noncomputable def hamiltonianChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      hamiltonianChecks := by
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => scalarChecks input && cycleCertificateChecks input)
  exact TM2AndOr.andOrComputableInPolyTime
    scalarChecksComputableInPolyTime
    cycleCertificateChecksComputableInPolyTime Bool.and

/-- One fixed polynomial-time TM2 computes the public serialized HAM-CYCLE
verifier on every raw certificate/instance pair. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => hamiltonianCycleVerifier input.1 input.2) := by
  let base : TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => GeneralCliqueVerifier.BaseChecks.baseChecks
        input.1 input.2) :=
    reencodeInput
      GeneralCliqueVerifier.BaseChecks.baseChecksComputableInPolyTime (by
        intro input
        rfl)
  let combined : TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      concreteHamiltonianCycleVerifier := by
    change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => GeneralCliqueVerifier.BaseChecks.baseChecks
        input.1 input.2 && hamiltonianChecks input)
    exact TM2AndOr.andOrComputableInPolyTime base
      hamiltonianChecksComputableInPolyTime Bool.and
  exact
    { tm := combined.tm
      inputAlphabet := combined.inputAlphabet
      outputAlphabet := combined.outputAlphabet
      time := combined.time
      outputsFun := fun input => by
        have output := combined.outputsFun input
        rw [concreteHamiltonianCycleVerifier_eq_public
          input.1 input.2] at output
        simpa using output }

/-- Named runtime polynomial of the complete verifier. -/
noncomputable def runtimePolynomial : Polynomial Nat :=
  computableInPolyTime.time

/-- The complete fixed HAM-CYCLE verifier machine. -/
noncomputable def machine : _root_.Turing.FinTM2 :=
  computableInPolyTime.tm

/-- Exact-output contract at the named polynomial runtime. -/
theorem machine_outputs (input : RawInput) :
    Nonempty (_root_.Turing.TM2OutputsInTime machine
      (List.map computableInPolyTime.inputAlphabet.invFun
        (rawEncoding input))
      (some (List.map computableInPolyTime.outputAlphabet.invFun
        (TM2Comp.boolEncoding
          (hamiltonianCycleVerifier input.1 input.2))))
      (runtimePolynomial.eval (rawEncoding input).length)) := by
  exact ⟨computableInPolyTime.outputsFun input⟩

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine
