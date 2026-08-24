import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Completeness

/-!
# VERTEX-COVER-to-CLIQUE soundness

A cover of size at most `k` leaves at least `|V| - k` uncovered vertices.
Choosing exactly that many vertices gives a clique in the complement graph.
-/

namespace CLRS
namespace Chapter34
namespace CliqueInstance

/-- A vertex cover in `I` yields a clique of size `|V| - k` in the graph
complement. -/
theorem complement_hasClique_of_hasVertexCover {I : CliqueInstance}
    (hcover : I.HasVertexCover) :
    I.complementForVertexCover.HasClique := by
  rcases hcover with ⟨cover, hcoverCard, hcoverBounded, hcoversEdges⟩
  have hcoverSubset : cover ⊆ Finset.range I.vertexCount := by
    intro v hv
    exact Finset.mem_range.mpr (hcoverBounded v hv)
  let outside := Finset.range I.vertexCount \ cover
  have houtsideCard : outside.card = I.vertexCount - cover.card := by
    exact card_range_sdiff hcoverSubset
  have htargetOutside : I.vertexCount - I.targetSize ≤ outside.card := by
    rw [houtsideCard]
    omega
  obtain ⟨vertices, hverticesOutside, hverticesCard⟩ :=
    Finset.exists_subset_card_eq htargetOutside
  refine ⟨vertices, ?_, ?_, ?_⟩
  · exact hverticesCard
  · intro v hv
    exact Finset.mem_range.mp
      (Finset.mem_sdiff.mp (hverticesOutside hv)).1
  · intro u hu v hv huv
    have huOutside := Finset.mem_sdiff.mp (hverticesOutside hu)
    have hvOutside := Finset.mem_sdiff.mp (hverticesOutside hv)
    rcases Nat.lt_or_gt_of_ne huv with huvlt | hvult
    · apply (I.complementForVertexCover.adj_iff_of_lt huvlt).2
      apply mem_vertexCoverComplementEdges_iff.mpr
      refine ⟨huvlt, Finset.mem_range.mp hvOutside.1, ?_⟩
      intro hedge
      rcases hcoversEdges (u, v) hedge with hucover | hvcover
      · exact huOutside.2 hucover
      · exact hvOutside.2 hvcover
    · apply (I.complementForVertexCover.adj_comm u v).2
      apply (I.complementForVertexCover.adj_iff_of_lt hvult).2
      apply mem_vertexCoverComplementEdges_iff.mpr
      refine ⟨hvult, Finset.mem_range.mp huOutside.1, ?_⟩
      intro hedge
      rcases hcoversEdges (v, u) hedge with hvcover | hucover
      · exact hvOutside.2 hvcover
      · exact huOutside.2 hucover

end CliqueInstance
end Chapter34
end CLRS
