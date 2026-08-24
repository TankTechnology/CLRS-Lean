import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ReverseSoundness

/-!
# VERTEX-COVER-to-CLIQUE completeness

The complement of a clique of size `|V| - k` has at most `k` vertices and
meets every source edge.
-/

namespace CLRS
namespace Chapter34
namespace CliqueInstance

/-- A clique of size `|V| - k` in the complement graph yields a vertex cover
of size at most `k` in the source graph. -/
theorem hasVertexCover_of_complement_hasClique {I : CliqueInstance}
    (hI : I.WellFormed)
    (hclique : I.complementForVertexCover.HasClique) :
    I.HasVertexCover := by
  rcases hclique with ⟨vertices, hcard, hbounded, hadj⟩
  have hverticesSubset : vertices ⊆ Finset.range I.vertexCount := by
    intro v hv
    exact Finset.mem_range.mpr (hbounded v hv)
  let cover := Finset.range I.vertexCount \ vertices
  have hcard' : vertices.card = I.vertexCount - I.targetSize := by
    simpa [complementForVertexCover] using hcard
  refine ⟨cover, ?_, ?_, ?_⟩
  · rw [card_range_sdiff hverticesSubset, hcard']
    omega
  · intro v hv
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hv).1
  · intro edge hedge
    rcases edge with ⟨u, v⟩
    have hedgeBounds := hI.2 (u, v) hedge
    by_cases hucover : u ∈ cover
    · exact Or.inl hucover
    · right
      refine Finset.mem_sdiff.mpr
        ⟨Finset.mem_range.mpr hedgeBounds.2, ?_⟩
      intro hvvertices
      have huvertices : u ∈ vertices := by
        by_contra hunot
        apply hucover
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_range.mpr
            (Nat.lt_trans hedgeBounds.1 hedgeBounds.2), hunot⟩
      have hadjuv := hadj u huvertices v hvvertices
        (Nat.ne_of_lt hedgeBounds.1)
      have hcomplementEdge :=
        (I.complementForVertexCover.adj_iff_of_lt hedgeBounds.1).mp hadjuv
      exact (mem_vertexCoverComplementEdges_iff.mp hcomplementEdge).2.2 hedge

end CliqueInstance
end Chapter34
end CLRS
