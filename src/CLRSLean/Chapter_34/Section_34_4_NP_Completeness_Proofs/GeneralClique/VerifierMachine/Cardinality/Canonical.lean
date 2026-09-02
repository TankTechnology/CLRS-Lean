import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.RoundTrip

/-!
# General CLIQUE verifier: canonical cardinality semantics

These lemmas connect the raw scan performed by the concrete controller to the
typed cardinality condition on canonical instance and certificate encodings.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

private theorem targetTicksUntilSeparator_prepend (count : Nat)
    (rest : List CliqueSym) :
    targetTicksUntilSeparator
        (prependCliqueTicks count (.fieldSep :: rest)) = some count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, targetTicksUntilSeparator, ih,
        Nat.add_comm]

private theorem rawTargetSize_prepend (count : Nat)
    (rest : List CliqueSym) :
    rawTargetSize (prependCliqueTicks count (.fieldSep :: rest)) =
      targetTicksUntilSeparator rest := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, rawTargetSize, ih]

private theorem count_vertexMark_prependCliqueTicks (count : Nat)
    (rest : List CliqueSym) :
    (prependCliqueTicks count rest).count .vertexMark =
      rest.count .vertexMark := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, ih]

@[simp] theorem encodeCliqueVertex_count_vertexMark (vertex : Nat) :
    (encodeCliqueVertex vertex).count .vertexMark = 1 := by
  simp [encodeCliqueVertex, count_vertexMark_prependCliqueTicks]

/-- Every canonical certificate record contributes exactly one vertex marker. -/
@[simp] theorem encodeCliqueCertificate_count_vertexMark
    (vertices : List Nat) :
    (encodeCliqueCertificate vertices).count .vertexMark = vertices.length := by
  induction vertices with
  | nil => simp [encodeCliqueCertificate]
  | cons vertex vertices ih =>
      have ih' : (vertices.flatMap encodeCliqueVertex).count .vertexMark =
          vertices.length := by
        simpa [encodeCliqueCertificate] using ih
      simp [encodeCliqueCertificate, ih']
      omega

/-- The raw target scan recovers the typed target size of a canonical instance. -/
@[simp] theorem rawTargetSize_encodeCliqueInstance (I : CliqueInstance) :
    rawTargetSize (encodeCliqueInstance I) = some I.targetSize := by
  simp [encodeCliqueInstance, rawTargetSize, rawTargetSize_prepend,
    targetTicksUntilSeparator_prepend]

/-- On canonical encodings, the concrete Boolean is exactly the typed
certificate-cardinality condition. -/
theorem cardinalityPass_encode_iff (I : CliqueInstance)
    (vertices : List Nat) :
    cardinalityPass (encodeCliqueCertificate vertices)
        (encodeCliqueInstance I) = true ↔
      vertices.length = I.targetSize := by
  simp [cardinalityPass]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality
