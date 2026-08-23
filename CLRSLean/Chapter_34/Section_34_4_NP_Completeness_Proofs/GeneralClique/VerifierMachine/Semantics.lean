import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairChecks
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Semantics

/-!
# General CLIQUE verifier: factored Boolean semantics

The parser, graph checks, vertex checks, and nested adjacency checks are joined
here without changing the already published function `cliqueVerifier`.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- The typed verifier split into the passes implemented by the concrete
machine. -/
def typedCliqueChecks (I : CliqueInstance) (vertices : List Nat) : Bool :=
  instanceWellFormedBool I &&
    vertexChecks I vertices &&
    pairwiseAdjacencyBool I vertices

/-- The factored typed checks are exactly the conjunction used by the public
Boolean verifier. -/
theorem typedCliqueChecks_eq_true_iff
    (I : CliqueInstance) (vertices : List Nat) :
    typedCliqueChecks I vertices = true ↔
      I.WellFormed ∧ I.ListRepresentsClique vertices := by
  simp only [typedCliqueChecks, Bool.and_eq_true,
    instanceWellFormedBool_eq_true_iff, vertexChecks_eq_true_iff,
    pairwiseAdjacencyBool_eq_true_iff]
  constructor
  · rintro ⟨⟨hwellFormed, hvertices⟩, hpairs⟩
    rcases hvertices with ⟨hnodup, hlength, hrange⟩
    refine ⟨hwellFormed, hnodup, hlength, hrange, ?_⟩
    exact (pairwise_adj_iff_all_distinct I hnodup).mp hpairs
  · rintro ⟨hwellFormed, hnodup, hlength, hrange, hpairs⟩
    exact ⟨⟨hwellFormed, hnodup, hlength, hrange⟩,
      (pairwise_adj_iff_all_distinct I hnodup).mpr hpairs⟩

/-- Boolean equality with the original typed `decide`, useful for exact
machine-output rewriting. -/
theorem typedCliqueChecks_eq_decide
    (I : CliqueInstance) (vertices : List Nat) :
    typedCliqueChecks I vertices =
      decide (I.WellFormed ∧ I.ListRepresentsClique vertices) := by
  apply Bool.eq_iff_iff.mpr
  simpa using typedCliqueChecks_eq_true_iff I vertices

/-- Raw verifier expressed through the explicit phase decomposition. -/
def factoredCliqueVerifier (certificate input : List CliqueSym) : Bool :=
  match decodeCliqueInstance input, decodeCliqueCertificate certificate with
  | some I, some vertices => typedCliqueChecks I vertices
  | _, _ => false

/-- The phased Boolean specification is definitionally faithful to the
previously fixed public verifier on every raw input. -/
theorem factoredCliqueVerifier_eq_cliqueVerifier
    (certificate input : List CliqueSym) :
    factoredCliqueVerifier certificate input =
      cliqueVerifier certificate input := by
  generalize hinput : decodeCliqueInstance input = instanceResult
  generalize hcertificate : decodeCliqueCertificate certificate =
    certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [factoredCliqueVerifier, cliqueVerifier, hinput, hcertificate,
      typedCliqueChecks_eq_decide]

/-- Exact all-input acceptance theorem for the phase decomposition. -/
theorem factoredCliqueVerifier_eq_true_iff
    (certificate input : List CliqueSym) :
    factoredCliqueVerifier certificate input = true ↔
      ∃ I vertices,
        decodeCliqueInstance input = some I ∧
        decodeCliqueCertificate certificate = some vertices ∧
        I.WellFormed ∧ I.ListRepresentsClique vertices := by
  rw [factoredCliqueVerifier_eq_cliqueVerifier]
  exact cliqueVerifier_eq_true_iff certificate input

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
