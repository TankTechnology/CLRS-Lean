import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.NP
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Hardness

/-! # General SUBSET-SUM is NP-complete -/

namespace CLRS.Chapter34

/-- The honest serialized textbook SUBSET-SUM language is NP-complete. -/
theorem SUBSETSUM_npComplete : NPComplete SUBSETSUM :=
  ⟨generalSUBSETSUM_polyTimeVerifiable, SUBSETSUM_npHard⟩

end CLRS.Chapter34
