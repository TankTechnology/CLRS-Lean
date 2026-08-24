import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.NP
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Reduction

/-! # General VERTEX-COVER is NP-complete -/

namespace CLRS.Chapter34

/-- The honest serialized graph-plus-`k` VERTEX-COVER language is
NP-complete. -/
theorem VERTEXCOVER_npComplete : NPComplete VERTEXCOVER :=
  ⟨generalVERTEXCOVER_polyTimeVerifiable, VERTEXCOVER_npHard⟩

end CLRS.Chapter34
