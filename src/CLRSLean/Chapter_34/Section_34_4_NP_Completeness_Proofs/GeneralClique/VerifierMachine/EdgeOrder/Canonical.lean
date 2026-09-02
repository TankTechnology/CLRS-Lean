import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Runtime

/-!
# General CLIQUE verifier: canonical normalized-edge semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder

private theorem rightResult_zero_true_prepend (right : Nat)
    (rest : List CliqueSym) :
    rightResult 0 true
        (prependCliqueTicks right (.recordEnd :: rest)) =
      edgesResult rest := by
  induction right with
  | zero => simp [prependCliqueTicks, rightResult]
  | succ right ih => simp [prependCliqueTicks, rightResult, ih]

private theorem rightResult_false_prepend (left right : Nat)
    (rest : List CliqueSym) :
    rightResult left false
        (prependCliqueTicks right (.recordEnd :: rest)) =
      (decide (left < right) && edgesResult rest) := by
  induction right generalizing left with
  | zero =>
      cases left <;> simp [prependCliqueTicks, rightResult]
  | succ right ih =>
      cases left with
      | zero =>
          simp [prependCliqueTicks, rightResult,
            rightResult_zero_true_prepend]
      | succ left =>
          simpa [prependCliqueTicks, rightResult] using ih left

private theorem leftResult_prepend (left count : Nat)
    (right : Nat) (rest : List CliqueSym) :
    leftResult count
        (prependCliqueTicks left
          (.pairSep :: prependCliqueTicks right (.recordEnd :: rest))) =
      rightResult (count + left) false
        (prependCliqueTicks right (.recordEnd :: rest)) := by
  induction left generalizing count with
  | zero => simp [prependCliqueTicks, leftResult]
  | succ left ih =>
      simp [prependCliqueTicks, leftResult, ih, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

private theorem edgesResult_encodeCliqueEdge_append
    (edge : Nat × Nat) (rest : List CliqueSym) :
    edgesResult (encodeCliqueEdge edge ++ rest) =
      (decide (edge.1 < edge.2) && edgesResult rest) := by
  rcases edge with ⟨left, right⟩
  simp only [encodeCliqueEdge, List.cons_append, edgesResult]
  rw [prependCliqueTicks_append]
  rw [List.cons_append, prependCliqueTicks_append]
  simp only [List.singleton_append]
  rw [leftResult_prepend]
  simp only [Nat.zero_add]
  exact rightResult_false_prepend left right rest

/-- The edge-suffix scan checks precisely that every canonical edge record is
stored in strictly increasing endpoint order. -/
theorem edgesResult_encode_edges (edges : List (Nat × Nat)) :
    edgesResult (edges.flatMap encodeCliqueEdge) =
      edges.all fun edge => decide (edge.1 < edge.2) := by
  induction edges with
  | nil => simp [edgesResult]
  | cons edge edges ih =>
      rw [List.flatMap_cons, edgesResult_encodeCliqueEdge_append, ih]
      simp

private theorem throughField_prepend (count : Nat)
    (next : List CliqueSym → Bool) (rest : List CliqueSym) :
    throughField next (prependCliqueTicks count (.fieldSep :: rest)) =
      next rest := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, throughField, ih]

/-- On a canonical graph encoding, the concrete pass is exactly the
normalization conjunct of `edgeBoundsBool`. -/
theorem edgeOrderPass_encode_iff (certificate : List CliqueSym)
    (I : CliqueInstance) :
    edgeOrderPass certificate (encodeCliqueInstance I) = true ↔
      ∀ edge ∈ I.edges, edge.1 < edge.2 := by
  simp only [edgeOrderPass, encodeCliqueInstance]
  rw [throughField_prepend, throughField_prepend, edgesResult_encode_edges]
  simp

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeOrder
