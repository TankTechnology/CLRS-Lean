import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement

/-!
# Size bounds for deterministic complement-pair enumeration

Each row contains at most `n` normalized pairs, the complete enumeration has
at most `n²` pairs, and filtering source edges cannot increase that length.
-/

namespace CLRS
namespace Chapter34

/-- A normalized-pair row contains at most the ambient number of vertices. -/
theorem vertexCoverNormalizedPairRow_length_le (n u : Nat) :
    (vertexCoverNormalizedPairRow n u).length ≤ n := by
  simp [vertexCoverNormalizedPairRow]
  omega

/-- The row-major enumeration contains at most one entry per ordered pair. -/
theorem vertexCoverNormalizedPairs_length_le (n : Nat) :
    (vertexCoverNormalizedPairs n).length ≤ n ^ 2 := by
  rw [vertexCoverNormalizedPairs, List.length_flatMap]
  have hrows :
      ((List.range n).map fun u => (vertexCoverNormalizedPairRow n u).length).sum ≤
        ((List.range n).map fun _ => n).sum := by
    apply List.sum_le_sum
    intro u _
    exact vertexCoverNormalizedPairRow_length_le n u
  simpa [Nat.pow_two] using hrows

/-- Removing source edges from the normalized-pair enumeration preserves the
quadratic length bound. -/
theorem vertexCoverComplementEdges_length_le (I : CliqueInstance) :
    (vertexCoverComplementEdges I).length ≤ I.vertexCount ^ 2 := by
  exact Nat.le_trans (List.length_filter_le _ _)
    (vertexCoverNormalizedPairs_length_le I.vertexCount)

end Chapter34
end CLRS
