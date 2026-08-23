import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Basic

/-!
# General CLIQUE verifier: canonical edge-lookup semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

private theorem leftResult_prepend (queryLeft queryRight candidate remaining : Nat)
    (equal : Bool) (rest : List CliqueSym) :
    leftResult queryLeft queryRight remaining equal
        (prependCliqueTicks candidate (.pairSep :: rest)) =
      rightResult queryLeft queryRight queryRight
        (equal && decide (candidate = remaining)) rest := by
  induction candidate generalizing remaining equal with
  | zero =>
      cases remaining <;> simp [prependCliqueTicks, leftResult]
  | succ candidate ih =>
      cases remaining with
      | zero =>
          simp [prependCliqueTicks, leftResult, ih]
      | succ remaining =>
          simpa [prependCliqueTicks, leftResult] using
            ih remaining equal

private theorem rightResult_prepend
    (queryLeft queryRight candidate remaining : Nat)
    (equal : Bool) (rest : List CliqueSym) :
    rightResult queryLeft queryRight remaining equal
        (prependCliqueTicks candidate (.recordEnd :: rest)) =
      ((equal && decide (candidate = remaining)) ||
        edgesResult queryLeft queryRight rest) := by
  induction candidate generalizing remaining equal with
  | zero =>
      cases remaining <;> simp [prependCliqueTicks, rightResult]
  | succ candidate ih =>
      cases remaining with
      | zero =>
          simp [prependCliqueTicks, rightResult, ih]
      | succ remaining =>
          simpa [prependCliqueTicks, rightResult] using
            ih remaining equal

private theorem edgesResult_encodeCliqueEdge_append
    (query edge : Nat × Nat) (rest : List CliqueSym) :
    edgesResult query.1 query.2 (encodeCliqueEdge edge ++ rest) =
      (decide (query = edge) || edgesResult query.1 query.2 rest) := by
  rcases query with ⟨queryLeft, queryRight⟩
  rcases edge with ⟨left, right⟩
  simp only [encodeCliqueEdge, List.cons_append, edgesResult]
  rw [prependCliqueTicks_append]
  rw [List.cons_append, prependCliqueTicks_append]
  simp only [List.singleton_append]
  rw [leftResult_prepend]
  rw [rightResult_prepend]
  simp [eq_comm]

/-- Scanning canonical edge records is exactly pair membership. -/
theorem edgesResult_encode_edges (query : Nat × Nat)
    (edges : List (Nat × Nat)) :
    edgesResult query.1 query.2 (edges.flatMap encodeCliqueEdge) =
      decide (query ∈ edges) := by
  induction edges with
  | nil => simp [edgesResult]
  | cons edge edges ih =>
      rw [List.flatMap_cons, edgesResult_encodeCliqueEdge_append, ih]
      simp

/-- The reusable edge scan implements the typed adjacency lookup below the
diagonal. -/
theorem edgesResult_encode_eq_adjacencyBool_of_lt
    (I : CliqueInstance) {u v : Nat} (huv : u < v) :
    edgesResult u v (I.edges.flatMap encodeCliqueEdge) =
      adjacencyBool I u v := by
  have h := edgesResult_encode_edges (u, v) I.edges
  simp only at h
  rw [h]
  simp [adjacencyBool, huv]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
