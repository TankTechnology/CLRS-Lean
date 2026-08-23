import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Specification
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.RoundTrip

/-!
# General CLIQUE verifier: canonical target-bound semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound

private theorem targetResult_prepend (targetSize : Nat)
    (rest : List CliqueSym) (vertexCount : Nat) :
    targetResult vertexCount
        (prependCliqueTicks targetSize (.fieldSep :: rest)) =
      decide (targetSize ≤ vertexCount) := by
  induction targetSize generalizing vertexCount with
  | zero => simp [prependCliqueTicks, targetResult]
  | succ targetSize ih =>
      cases vertexCount with
      | zero => simp [prependCliqueTicks, targetResult]
      | succ vertexCount =>
          simp [prependCliqueTicks, targetResult, ih]

private theorem vertexResult_prepend (vertexTicks count : Nat)
    (rest : List CliqueSym) :
    vertexResult count
        (prependCliqueTicks vertexTicks (.fieldSep :: rest)) =
      targetResult (count + vertexTicks) rest := by
  induction vertexTicks generalizing count with
  | zero => simp [prependCliqueTicks, vertexResult]
  | succ vertexTicks ih =>
      simp [prependCliqueTicks, vertexResult, ih, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- On a canonical graph serialization, the concrete pass is exactly the
typed target-size bound, independently of the certificate. -/
theorem targetBoundPass_encode_iff (certificate : List CliqueSym)
    (I : CliqueInstance) :
    targetBoundPass certificate (encodeCliqueInstance I) = true ↔
      I.targetSize ≤ I.vertexCount := by
  simp only [targetBoundPass, encodeCliqueInstance]
  rw [vertexResult_prepend]
  simp only [Nat.zero_add]
  rw [targetResult_prepend]
  simp

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.TargetBound
