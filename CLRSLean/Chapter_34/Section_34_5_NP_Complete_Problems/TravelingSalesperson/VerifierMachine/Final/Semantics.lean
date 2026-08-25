import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.Final.Basic
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.Semantics
import Mathlib.Tactic

/-! # Decision-TSP verifier: exact semantics -/

namespace CLRS.Chapter34.Turing.TSPVerifier.Final

private theorem baseCheck_eq_true_iff_exists
    (certificate : List TSPSym) (data : TSPData) :
    UnaryBaseInput.baseCheck (certificate, encodeTSPData data) = true ↔
      ∃ vertices,
        certificate = UnaryCertificate.encode vertices ∧
        ∀ vertex ∈ vertices, vertex < vertices.length := by
  constructor
  · intro hbase
    have hsyntax :
        GeneralCliqueVerifier.SyntaxPass.syntaxPass
            (UnaryBaseInput.baseInput
              (certificate, encodeTSPData data)).1
            (UnaryBaseInput.baseInput
              (certificate, encodeTSPData data)).2 = true := by
      exact (Bool.and_eq_true_iff.mp (by
        simpa [UnaryBaseInput.baseCheck,
          GeneralCliqueVerifier.BaseChecks.baseChecks] using hbase)).1
    rcases (GeneralCliqueVerifier.SyntaxPass.syntaxPass_eq_true_iff _ _).1
        hsyntax with ⟨⟨vertices, hdecode⟩, _⟩
    have hcertificate : certificate = UnaryCertificate.encode vertices :=
      UnaryCertificate.eq_encode_of_decode_toCliqueCertificate_eq_some
        certificate vertices hdecode
    subst certificate
    exact ⟨vertices, rfl,
      (UnaryBaseInput.baseCheck_encode_iff vertices data).1 hbase⟩
  · rintro ⟨vertices, rfl, hrange⟩
    exact (UnaryBaseInput.baseCheck_encode_iff vertices data).2 hrange

@[simp] theorem cardinalityCheck_unary_encode
    (vertices : List Nat) (data : TSPData) :
    StructuralChecks.cardinalityCheck
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      decide (vertices.length = data.vertexCount) := by
  simp [StructuralChecks.cardinalityCheck,
    FieldCount.certificateCountBits, encodeBinaryNat_injective.eq_iff]

@[simp] theorem matrixShapeCheck_unary_encode
    (vertices : List Nat) (data : TSPData) :
    StructuralChecks.matrixShapeCheck
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      decide (vertices.length ^ 2 = data.weights.length) := by
  simp [StructuralChecks.matrixShapeCheck, SquareCount.squareCountBits,
    SquareCount.squareTicks, encodeBinaryNat_injective.eq_iff]

@[simp] theorem minimumVertexCountCheck_unary_encode
    (vertices : List Nat) (data : TSPData) :
    StructuralChecks.minimumVertexCountCheck
        (UnaryCertificate.encode vertices, encodeTSPData data) = true ↔
      3 ≤ data.vertexCount := by
  exact StructuralChecks.minimumVertexCountCheck_encode data vertices

/-- On canonical unary certificates and canonical compact instances, every
concrete branch is exactly the textbook tour predicate. -/
theorem concreteTSPVerifier_encode_iff
    (vertices : List Nat) (data : TSPData) :
    concreteTSPVerifier
        (UnaryCertificate.encode vertices, encodeTSPData data) = true ↔
      data.WellFormed ∧ data.toInstance.ListRepresentsTour vertices := by
  constructor
  · intro haccept
    have hparts :
        (StructuralChecks.cardinalityCheck
            (UnaryCertificate.encode vertices, encodeTSPData data) = true ∧
          (StructuralChecks.matrixShapeCheck
              (UnaryCertificate.encode vertices, encodeTSPData data) = true ∧
            StructuralChecks.minimumVertexCountCheck
              (UnaryCertificate.encode vertices, encodeTSPData data) = true)) ∧
        ((UnaryBaseInput.baseCheck
              (UnaryCertificate.encode vertices, encodeTSPData data) = true ∧
            UnaryBaseInput.nodupCheck
              (UnaryCertificate.encode vertices, encodeTSPData data) = true) ∧
          (SymmetryCheck.symmetryCheck
              (UnaryCertificate.encode vertices, encodeTSPData data) = true ∧
            BudgetCheck.costCheck
              (UnaryCertificate.encode vertices, encodeTSPData data) = true)) := by
      simpa [concreteTSPVerifier, structuralChecks, tourShapeChecks,
        weightedChecks, Syntax.instanceSyntax_encode] using haccept
    rcases hparts with
      ⟨⟨hcount, hshape, hminimum⟩,
        ⟨⟨hrange, hnodup⟩, ⟨hsymmetry, hcost⟩⟩⟩
    have hcount' : vertices.length = data.vertexCount := by
      exact of_decide_eq_true (by simpa using hcount)
    have hshape' : data.weights.length =
        data.vertexCount * data.vertexCount := by
      have hsquare : vertices.length ^ 2 = data.weights.length :=
        of_decide_eq_true (by simpa using hshape)
      rw [← hcount']
      simpa [pow_two] using hsquare.symm
    have hminimum' : 3 ≤ data.vertexCount :=
      (minimumVertexCountCheck_unary_encode vertices data).1 hminimum
    have hrange' : ∀ vertex ∈ vertices,
        vertex < data.vertexCount := by
      intro vertex hvertex
      rw [← hcount']
      exact (UnaryBaseInput.baseCheck_encode_iff vertices data).1 hrange
        vertex hvertex
    have hnodup' : vertices.Nodup :=
      (UnaryBaseInput.nodupCheck_encode_iff vertices data).1 hnodup
    have hsymmetry' : TSPData.OrientationPairsEqual
        (data.weights.drop data.vertexCount) :=
      (SymmetryCheck.symmetryCheck_encode_iff vertices data hcount'
        hshape').1 hsymmetry
    have hwellFormed : data.WellFormed := ⟨hshape', hsymmetry'⟩
    have hcost' : data.toInstance.tourCost vertices ≤ data.budget :=
      (BudgetCheck.costCheck_encode_iff vertices data hwellFormed
        (by omega) hnodup' hcount' hrange').1 hcost
    exact ⟨hwellFormed, hminimum', hnodup', hcount', hrange', hcost'⟩
  · rintro ⟨hwellFormed, hminimum, hnodup, hcount, hrange, hcost⟩
    change 3 ≤ data.vertexCount at hminimum
    change vertices.length = data.vertexCount at hcount
    change (∀ vertex ∈ vertices, vertex < data.vertexCount) at hrange
    change data.toInstance.tourCost vertices ≤ data.budget at hcost
    have hshape : vertices.length ^ 2 = data.weights.length := by
      rw [hcount, pow_two]
      exact hwellFormed.1.symm
    have hbase : UnaryBaseInput.baseCheck
        (UnaryCertificate.encode vertices, encodeTSPData data) = true :=
      (UnaryBaseInput.baseCheck_encode_iff vertices data).2 (by
        intro vertex hvertex
        rw [hcount]
        exact hrange vertex hvertex)
    have hsymmetry :=
      (SymmetryCheck.symmetryCheck_encode_iff vertices data hcount
        hwellFormed.1).2 hwellFormed.2
    have hbudget :=
      (BudgetCheck.costCheck_encode_iff vertices data hwellFormed
        (by omega) hnodup hcount hrange).2 hcost
    have hshapeData : data.vertexCount ^ 2 = data.weights.length := by
      simpa [hcount] using hshape
    simp [concreteTSPVerifier, structuralChecks, tourShapeChecks,
      weightedChecks, Syntax.instanceSyntax_encode, hcount,
      hshapeData, hminimum, hbase, hnodup, hsymmetry, hbudget]

/-- Exact acceptance theorem on arbitrary raw inputs.  Accepted instance words
are canonical by the syntax branch, while acceptance of the reused CLIQUE
base checker makes the certificate a canonical unary tour word. -/
theorem concreteTSPVerifier_eq_true_iff
    (certificate input : List TSPSym) :
    concreteTSPVerifier (certificate, input) = true ↔
      ∃ data vertices,
        decodeTSPData input = some data ∧
        certificate = UnaryCertificate.encode vertices ∧
        data.WellFormed ∧ data.toInstance.ListRepresentsTour vertices := by
  constructor
  · intro haccept
    change (Syntax.instanceSyntax input &&
        (structuralChecks (certificate, input) &&
          (tourShapeChecks (certificate, input) &&
            weightedChecks (certificate, input)))) = true at haccept
    have hsyntax : Syntax.instanceSyntax input = true := by
      exact (Bool.and_eq_true_iff.mp haccept).1
    rcases (Syntax.instanceSyntax_eq_true_iff_exists_decode input).1 hsyntax
      with ⟨data, hdecode⟩
    have hcanonical := encodeTSPData_eq_of_decode_eq_some input data hdecode
    have haccept' : concreteTSPVerifier
        (certificate, encodeTSPData data) = true := by
      rw [hcanonical]
      exact haccept
    have hbase : UnaryBaseInput.baseCheck
        (certificate, encodeTSPData data) = true := by
      change (Syntax.instanceSyntax (encodeTSPData data) &&
          (structuralChecks (certificate, encodeTSPData data) &&
            (tourShapeChecks (certificate, encodeTSPData data) &&
              weightedChecks (certificate, encodeTSPData data)))) = true
        at haccept'
      have hparts := Bool.and_eq_true_iff.mp haccept'
      have hsemantic := Bool.and_eq_true_iff.mp hparts.2
      have htourWeighted := Bool.and_eq_true_iff.mp hsemantic.2
      exact (Bool.and_eq_true_iff.mp htourWeighted.1).1
    rcases (baseCheck_eq_true_iff_exists certificate data).1 hbase with
      ⟨vertices, hcertificate, _⟩
    subst certificate
    have htyped := (concreteTSPVerifier_encode_iff vertices data).1 haccept'
    exact ⟨data, vertices, hdecode, rfl, htyped⟩
  · rintro ⟨data, vertices, hdecode, rfl, htyped⟩
    have hcanonical := encodeTSPData_eq_of_decode_eq_some input data hdecode
    rw [← hcanonical]
    exact (concreteTSPVerifier_encode_iff vertices data).2 htyped

end CLRS.Chapter34.Turing.TSPVerifier.Final
