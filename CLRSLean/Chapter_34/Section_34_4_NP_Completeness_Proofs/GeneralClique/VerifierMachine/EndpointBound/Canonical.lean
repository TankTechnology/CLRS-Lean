import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Basic

/-!
# General CLIQUE verifier: canonical endpoint-bound semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound

/-- Typed Boolean specification for the right-endpoint range condition. -/
def endpointsWithinBool (vertexCount : Nat)
    (edges : List (Nat × Nat)) : Bool :=
  edges.all fun edge => decide (edge.2 < vertexCount)

theorem endpointsWithinBool_eq_true_iff (vertexCount : Nat)
    (edges : List (Nat × Nat)) :
    endpointsWithinBool vertexCount edges = true ↔
      ∀ edge ∈ edges, edge.2 < vertexCount := by
  simp [endpointsWithinBool]

private theorem rightResult_prepend (right remaining spent : Nat)
    (rest : List CliqueSym) :
    rightResult remaining spent
        (prependCliqueTicks right (.recordEnd :: rest)) =
      (decide (right < remaining) &&
        edgesResult (remaining + spent) rest) := by
  induction right generalizing remaining spent with
  | zero =>
      cases remaining <;> simp [prependCliqueTicks, rightResult]
  | succ right ih =>
      cases remaining with
      | zero => simp [prependCliqueTicks, rightResult]
      | succ remaining =>
          simp only [prependCliqueTicks, rightResult]
          rw [ih]
          have hsum : remaining + (spent + 1) =
              remaining + 1 + spent := by omega
          rw [hsum]
          simp

private theorem leftResult_prepend (left vertexCount : Nat)
    (rest : List CliqueSym) :
    leftResult vertexCount
        (prependCliqueTicks left (.pairSep :: rest)) =
      rightResult vertexCount 0 rest := by
  induction left with
  | zero => rfl
  | succ left ih => simp [prependCliqueTicks, leftResult, ih]

private theorem edgesResult_flatMap (vertexCount : Nat)
    (edges : List (Nat × Nat)) :
    edgesResult vertexCount (edges.flatMap encodeCliqueEdge) =
      endpointsWithinBool vertexCount edges := by
  induction edges with
  | nil => simp [edgesResult, endpointsWithinBool]
  | cons edge edges ih =>
      rcases edge with ⟨left, right⟩
      rw [List.flatMap_cons]
      simp only [encodeCliqueEdge, List.cons_append,
        prependCliqueTicks_append, edgesResult]
      rw [leftResult_prepend, rightResult_prepend]
      simp only [Nat.add_zero, List.nil_append, endpointsWithinBool,
        List.all_cons]
      rw [ih]
      rfl

private theorem targetFieldResult_prepend (targetSize vertexCount : Nat)
    (rest : List CliqueSym) :
    targetFieldResult vertexCount
        (prependCliqueTicks targetSize (.fieldSep :: rest)) =
      edgesResult vertexCount rest := by
  induction targetSize with
  | zero => rfl
  | succ targetSize ih =>
      simp [prependCliqueTicks, targetFieldResult, ih]

private theorem vertexFieldResult_prepend (vertexTicks loaded : Nat)
    (rest : List CliqueSym) :
    vertexFieldResult loaded
        (prependCliqueTicks vertexTicks (.fieldSep :: rest)) =
      targetFieldResult (loaded + vertexTicks) rest := by
  induction vertexTicks generalizing loaded with
  | zero => simp [prependCliqueTicks, vertexFieldResult]
  | succ vertexTicks ih =>
      simp [prependCliqueTicks, vertexFieldResult, ih, Nat.add_comm,
        Nat.add_left_comm]

/-- On canonical instances, the pass accepts exactly when every stored right
endpoint is smaller than the declared vertex count. -/
theorem endpointBoundPass_encode_iff (certificate : List CliqueSym)
    (I : CliqueInstance) :
    endpointBoundPass certificate (encodeCliqueInstance I) = true ↔
      ∀ edge ∈ I.edges, edge.2 < I.vertexCount := by
  simp only [endpointBoundPass, encodeCliqueInstance]
  rw [vertexFieldResult_prepend]
  simp only [Nat.zero_add]
  rw [targetFieldResult_prepend, edgesResult_flatMap]
  exact endpointsWithinBool_eq_true_iff I.vertexCount I.edges

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EndpointBound
