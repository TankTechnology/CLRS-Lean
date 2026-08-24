import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawTotal
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.NPCompleteness

/-! # Decision-TSP hardness -/

namespace CLRS.Chapter34

/-- The complete-matrix `1/2`-weight construction is a concrete polynomial-
time many-one reduction from honest serialized HAM-CYCLE to decision-TSP. -/
theorem HAMCYCLE_reducible_to_TSP :
    PolyTimeReducible HAMCYCLE TSP := by
  refine ⟨TSPReduction.rawHamiltonianToTSP,
    ⟨Turing.TSPReduction.RawTotal.computableInPolyTime⟩, ?_⟩
  intro input
  exact TSPReduction.rawHamiltonianToTSP_correct input

/-- Honest serialized decision-TSP is NP-hard. -/
theorem TSP_npHard : NPHard TSP :=
  NPHard.of_reducible HAMCYCLE_npHard HAMCYCLE_reducible_to_TSP

end CLRS.Chapter34
