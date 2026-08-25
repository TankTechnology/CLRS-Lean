import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.NP
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Hardness

/-! # General decision-TSP is NP-complete -/

namespace CLRS.Chapter34

/-- The honest serialized decision-TSP language is NP-complete. -/
theorem TSP_npComplete : NPComplete TSP :=
  ⟨generalTSP_polyTimeVerifiable, TSP_npHard⟩

end CLRS.Chapter34
