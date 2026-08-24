import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement

/-!
# Size bounds for deterministic complement-pair enumeration

Each newly introduced upper endpoint contributes at most `n` pairs, the
complete enumeration has at most `n²` pairs, and filtering source edges cannot
increase that length.
-/

namespace CLRS
namespace Chapter34

/-- A normalized-pair row contains at most the ambient number of vertices. -/
theorem vertexCoverNormalizedPairRow_length_le (n u : Nat) :
    (vertexCoverNormalizedPairRow n u).length ≤ n := by
  simp [vertexCoverNormalizedPairRow]
  omega

/-- The canonical enumeration contains at most one entry per ordered pair. -/
theorem vertexCoverNormalizedPairs_length_le (n : Nat) :
    (vertexCoverNormalizedPairs n).length ≤ n ^ 2 := by
  induction n with
  | zero => simp [vertexCoverNormalizedPairs]
  | succ n ih =>
      simp only [vertexCoverNormalizedPairs, List.length_append,
        List.length_map, List.length_range]
      nlinarith

/-- Removing source edges from the normalized-pair enumeration preserves the
quadratic length bound. -/
theorem vertexCoverComplementEdges_length_le (I : CliqueInstance) :
    (vertexCoverComplementEdges I).length ≤ I.vertexCount ^ 2 := by
  exact Nat.le_trans (List.length_filter_le _ _)
    (vertexCoverNormalizedPairs_length_le I.vertexCount)

end Chapter34
end CLRS
