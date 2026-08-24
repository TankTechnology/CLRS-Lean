import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.Total
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Completeness

/-! # Concrete polynomial-time CLIQUE-to-VERTEX-COVER reduction -/

namespace CLRS.Chapter34

/-- The textbook graph-complement construction is a concrete polynomial-time
many-one reduction from general CLIQUE to VERTEX-COVER. -/
theorem generalCLIQUE_reducible_to_VERTEXCOVER :
    PolyTimeReducible GeneralCLIQUE VERTEXCOVER := by
  refine ⟨cliqueToVertexCoverMap,
    ⟨Turing.VertexCover.ComplementMachine.Total.computableInPolyTime⟩, ?_⟩
  intro input
  exact (cliqueToVertexCoverMap_mem_VERTEXCOVER_iff input).symm

/-- General VERTEX-COVER is NP-hard. -/
theorem VERTEXCOVER_npHard : NPHard VERTEXCOVER :=
  NPHard.of_reducible generalCLIQUE_npHard
    generalCLIQUE_reducible_to_VERTEXCOVER

end CLRS.Chapter34
