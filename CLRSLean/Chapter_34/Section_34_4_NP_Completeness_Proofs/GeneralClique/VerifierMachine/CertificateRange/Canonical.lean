import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Basic

/-!
# General CLIQUE verifier: canonical certificate-range semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange

/-- Typed Boolean specification for certificate vertex range. -/
def verticesWithinBool (vertexCount : Nat) (vertices : List Nat) : Bool :=
  vertices.all fun vertex => decide (vertex < vertexCount)

theorem verticesWithinBool_eq_true_iff (vertexCount : Nat)
    (vertices : List Nat) :
    verticesWithinBool vertexCount vertices = true ↔
      ∀ vertex ∈ vertices, vertex < vertexCount := by
  simp [verticesWithinBool]

private theorem vertexResult_prepend (vertex remaining spent : Nat)
    (rest : List CliqueSym) :
    vertexResult remaining spent
        (prependCliqueTicks vertex (.recordEnd :: rest)) =
      (decide (vertex < remaining) &&
        verticesResult (remaining + spent) rest) := by
  induction vertex generalizing remaining spent with
  | zero => cases remaining <;> simp [prependCliqueTicks, vertexResult]
  | succ vertex ih =>
      cases remaining with
      | zero => simp [prependCliqueTicks, vertexResult]
      | succ remaining =>
          simp only [prependCliqueTicks, vertexResult]
          rw [ih]
          have hsum : remaining + (spent + 1) =
              remaining + 1 + spent := by omega
          rw [hsum]
          simp

private theorem verticesResult_flatMap (vertexCount : Nat)
    (vertices : List Nat) :
    verticesResult vertexCount (vertices.flatMap encodeCliqueVertex) =
      verticesWithinBool vertexCount vertices := by
  induction vertices with
  | nil => simp [verticesResult, verticesWithinBool]
  | cons vertex vertices ih =>
      rw [List.flatMap_cons]
      simp only [encodeCliqueVertex, List.cons_append,
        prependCliqueTicks_append, verticesResult]
      rw [vertexResult_prepend]
      simp only [Nat.add_zero, List.nil_append, verticesWithinBool,
        List.all_cons]
      rw [ih]
      rfl

private theorem vertexFieldResult_prepend (vertexTicks loaded : Nat)
    (certificate rest : List CliqueSym) :
    vertexFieldResult certificate loaded
        (prependCliqueTicks vertexTicks (.fieldSep :: rest)) =
      certificatePayloadResult (loaded + vertexTicks) certificate := by
  induction vertexTicks generalizing loaded with
  | zero => simp [prependCliqueTicks, vertexFieldResult]
  | succ vertexTicks ih =>
      simp [prependCliqueTicks, vertexFieldResult, ih, Nat.add_comm,
        Nat.add_left_comm]

/-- On canonical pairs, the pass accepts exactly when every certificate vertex
is below the declared vertex count. -/
theorem certificateRangePass_encode_iff (I : CliqueInstance)
    (vertices : List Nat) :
    certificateRangePass (encodeCliqueCertificate vertices)
        (encodeCliqueInstance I) = true ↔
      ∀ vertex ∈ vertices, vertex < I.vertexCount := by
  simp only [certificateRangePass, encodeCliqueInstance]
  rw [vertexFieldResult_prepend]
  simp only [Nat.zero_add, certificatePayloadResult,
    encodeCliqueCertificate]
  rw [verticesResult_flatMap]
  exact verticesWithinBool_eq_true_iff I.vertexCount vertices

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.CertificateRange
