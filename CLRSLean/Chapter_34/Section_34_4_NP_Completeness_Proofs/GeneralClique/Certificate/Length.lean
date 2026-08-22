import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Semantics

/-!
# Polynomial certificate bound for general CLIQUE

A finite-set clique is serialized through its duplicate-free list.  Unary
vertex records remain quadratically bounded by the raw instance length.
-/

namespace CLRS
namespace Chapter34

/-- Exact decomposition of a certificate into its leading marker and records. -/
theorem encodeCliqueCertificate_length (vertices : List Nat) :
    (encodeCliqueCertificate vertices).length =
      1 + (vertices.flatMap encodeCliqueVertex).length := by
  simp [encodeCliqueCertificate]
  omega

/-- If every vertex is below {lit}`bound`, the concatenated unary records cost at
most one {lit}`bound + 1` block per vertex. -/
theorem flatMap_encodeCliqueVertex_length_le {vertices : List Nat} {bound : Nat}
    (hbound : ∀ v ∈ vertices, v < bound) :
    (vertices.flatMap encodeCliqueVertex).length ≤
      vertices.length * (bound + 1) := by
  induction vertices with
  | nil => simp
  | cons vertex vertices ih =>
      have hvertex : vertex + 2 ≤ bound + 1 := by
        have := hbound vertex (by simp)
        omega
      have htail : (vertices.flatMap encodeCliqueVertex).length ≤
          vertices.length * (bound + 1) := by
        apply ih
        intro v hv
        exact hbound v (by simp [hv])
      simp only [List.flatMap_cons, List.length_append,
        encodeCliqueVertex_length, List.length_cons]
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add hvertex htail

/-- Membership in general CLIQUE supplies a canonical accepted certificate of
quadratic physical length. -/
theorem exists_bounded_cliqueCertificate_of_mem {input : List CliqueSym}
    (hmem : input ∈ GeneralCLIQUE) :
    ∃ certificate,
      certificate.length ≤ (input.length + 1) ^ 2 ∧
      cliqueVerifier certificate input = true := by
  rcases hmem with ⟨I, hdecode, hwellFormed, hclique⟩
  rcases I.exists_listRepresentsClique_of_hasClique hclique with
    ⟨vertices, hvertices⟩
  refine ⟨encodeCliqueCertificate vertices, ?_, ?_⟩
  · rcases hvertices with ⟨_, hcard, hbound, _⟩
    have hrecords := flatMap_encodeCliqueVertex_length_le hbound
    have hfields := decodeCliqueInstance_fields_le_length hdecode
    rw [encodeCliqueCertificate_length]
    nlinarith
  · exact (cliqueVerifier_eq_true_iff _ _).2
      ⟨I, vertices, hdecode, decode_encodeCliqueCertificate vertices,
        hwellFormed, hvertices⟩

/-- Exact certificate characterization of general CLIQUE, including the
quadratic certificate-size polynomial needed by {lit}`PolyTimeVerifiable`. -/
theorem mem_generalCLIQUE_iff_exists_certificate (input : List CliqueSym) :
    input ∈ GeneralCLIQUE ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 1) ^ 2 ∧
        cliqueVerifier certificate input = true := by
  constructor
  · exact exists_bounded_cliqueCertificate_of_mem
  · rintro ⟨certificate, _, hverify⟩
    rcases (cliqueVerifier_eq_true_iff certificate input).1 hverify with
      ⟨I, vertices, hdecode, _, hwellFormed, hvertices⟩
    exact ⟨I, hdecode, hwellFormed, I.hasClique_of_listRepresentsClique hvertices⟩

end Chapter34
end CLRS
