import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement.PairBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Length

/-!
# Encoding-size bounds for the deterministic graph complement

Unary endpoints make one complement edge linear in the vertex count.  Together
with the quadratic pair bound, the complete encoded complement is cubic.
-/

namespace CLRS
namespace Chapter34

private theorem sum_map_le_mul {α : Type} (xs : List α) (f : α → Nat)
    (bound : Nat) (hbound : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have htail : ∀ y ∈ xs, f y ≤ bound := by
        intro y hy
        exact hbound y (by simp [hy])
      have hrest := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- The aggregate unary cost of complement edges is cubic in the vertex
count. -/
theorem cliqueEdgesEncodingLength_vertexCoverComplementEdges_le
    (I : CliqueInstance) :
    cliqueEdgesEncodingLength (vertexCoverComplementEdges I) ≤
      I.vertexCount ^ 2 * (2 * I.vertexCount + 3) := by
  let edges := vertexCoverComplementEdges I
  have hpoint : ∀ edge ∈ edges,
      edge.1 + edge.2 + 3 ≤ 2 * I.vertexCount + 3 := by
    intro edge hedge
    rcases edge with ⟨u, v⟩
    have hmem := mem_vertexCoverComplementEdges_iff.mp hedge
    omega
  have hsum := sum_map_le_mul edges
    (fun edge => edge.1 + edge.2 + 3) (2 * I.vertexCount + 3) hpoint
  have hlength := vertexCoverComplementEdges_length_le I
  exact Nat.le_trans hsum (Nat.mul_le_mul_right _ hlength)

/-- The complete unary graph encoding of the deterministic complement has a
uniform cubic bound. -/
theorem encode_complementForVertexCover_length_le (I : CliqueInstance) :
    (encodeCliqueInstance I.complementForVertexCover).length ≤
      5 * (I.vertexCount + 1) ^ 3 := by
  rw [encodeCliqueInstance_length]
  have hedges := cliqueEdgesEncodingLength_vertexCoverComplementEdges_le I
  simp only [CliqueInstance.complementForVertexCover]
  nlinarith [Nat.sub_le I.vertexCount I.targetSize]

end Chapter34
end CLRS
