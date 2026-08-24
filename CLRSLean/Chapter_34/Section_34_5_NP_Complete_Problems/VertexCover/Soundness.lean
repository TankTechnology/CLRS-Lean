import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement

/-!
# Soundness of the CLIQUE-to-VERTEX-COVER complement reduction

The complement of a clique is a vertex cover in the complemented graph.  This
module proves that direction on typed graph instances, including the exact
finite-cardinality bookkeeping.
-/

namespace CLRS
namespace Chapter34
namespace CliqueInstance

/-- Removing a bounded vertex set from the full vertex range leaves exactly
`n - |S|` vertices. -/
theorem card_range_sdiff {n : Nat} {vertices : Finset Nat}
    (hvertices : vertices ⊆ Finset.range n) :
    (Finset.range n \ vertices).card = n - vertices.card := by
  rw [Finset.card_sdiff_of_subset hvertices, Finset.card_range]

/-- A clique in `I` yields a vertex cover in the graph complement, with target
`|V| - k`. -/
theorem complement_hasVertexCover_of_hasClique {I : CliqueInstance}
    (hclique : I.HasClique) :
    I.complementForVertexCover.HasVertexCover := by
  rcases hclique with ⟨vertices, hcard, hbounded, hadj⟩
  let cover := Finset.range I.vertexCount \ vertices
  have hvertices : vertices ⊆ Finset.range I.vertexCount := by
    intro v hv
    exact Finset.mem_range.mpr (hbounded v hv)
  refine ⟨cover, ?_, ?_⟩
  · change cover.card ≤ I.vertexCount - I.targetSize
    rw [card_range_sdiff hvertices, hcard]
  · refine ⟨?_, ?_⟩
    · intro v hv
      exact Finset.mem_range.mp (Finset.mem_sdiff.mp hv).1
    · intro edge hedge
      rcases edge with ⟨u, v⟩
      have hcomplement := mem_vertexCoverComplementEdges_iff.mp hedge
      by_cases hucover : u ∈ cover
      · exact Or.inl hucover
      · right
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hcomplement.2.1, ?_⟩
        intro hvvertices
        have huvertices : u ∈ vertices := by
          by_contra hunot
          apply hucover
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_range.mpr (Nat.lt_trans hcomplement.1 hcomplement.2.1), hunot⟩
        have hadjuv := hadj u huvertices v hvvertices
          (Nat.ne_of_lt hcomplement.1)
        exact hcomplement.2.2 ((I.adj_iff_of_lt hcomplement.1).mp hadjuv)

end CliqueInstance
end Chapter34
end CLRS
