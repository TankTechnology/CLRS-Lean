import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Soundness

/-!
# Completeness of the CLIQUE-to-VERTEX-COVER complement reduction

A small vertex cover in the complemented graph leaves at least `k` uncovered
vertices.  Any `k` of them form a clique in the source graph, because a source
nonedge would be a complement edge missed by the cover.
-/

namespace CLRS
namespace Chapter34
namespace CliqueInstance

/-- A vertex cover of the complemented graph yields a clique of the requested
size in the source graph. -/
theorem hasClique_of_complement_hasVertexCover {I : CliqueInstance}
    (hI : I.WellFormed)
    (hcover : I.complementForVertexCover.HasVertexCover) :
    I.HasClique := by
  rcases hcover with ⟨cover, hcoverCard, hcoverBounded, hcoversEdges⟩
  have hcoverSubset : cover ⊆ Finset.range I.vertexCount := by
    intro v hv
    exact Finset.mem_range.mpr (hcoverBounded v hv)
  let outside := Finset.range I.vertexCount \ cover
  have houtsideCard : outside.card = I.vertexCount - cover.card := by
    exact card_range_sdiff hcoverSubset
  have htargetOutside : I.targetSize ≤ outside.card := by
    rw [houtsideCard]
    change cover.card ≤ I.vertexCount - I.targetSize at hcoverCard
    have htargetBound : I.targetSize ≤ I.vertexCount := hI.1
    omega
  obtain ⟨vertices, hverticesOutside, hverticesCard⟩ :=
    Finset.exists_subset_card_eq htargetOutside
  refine ⟨vertices, hverticesCard, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_range.mp
      (Finset.mem_sdiff.mp (hverticesOutside hv)).1
  · intro u hu v hv huv
    have huOutside := Finset.mem_sdiff.mp (hverticesOutside hu)
    have hvOutside := Finset.mem_sdiff.mp (hverticesOutside hv)
    rcases Nat.lt_or_gt_of_ne huv with huvlt | hvult
    · apply (I.adj_iff_of_lt huvlt).2
      by_contra hnonedge
      have hcomplementEdge : (u, v) ∈ vertexCoverComplementEdges I :=
        mem_vertexCoverComplementEdges_iff.mpr
          ⟨huvlt, Finset.mem_range.mp hvOutside.1, hnonedge⟩
      rcases hcoversEdges (u, v) hcomplementEdge with hucover | hvcover
      · exact huOutside.2 hucover
      · exact hvOutside.2 hvcover
    · apply (I.adj_comm u v).2
      apply (I.adj_iff_of_lt hvult).2
      by_contra hnonedge
      have hcomplementEdge : (v, u) ∈ vertexCoverComplementEdges I :=
        mem_vertexCoverComplementEdges_iff.mpr
          ⟨hvult, Finset.mem_range.mp huOutside.1, hnonedge⟩
      rcases hcoversEdges (v, u) hcomplementEdge with hvcover | hucover
      · exact hvOutside.2 hvcover
      · exact huOutside.2 hucover

end CliqueInstance
end Chapter34
end CLRS
