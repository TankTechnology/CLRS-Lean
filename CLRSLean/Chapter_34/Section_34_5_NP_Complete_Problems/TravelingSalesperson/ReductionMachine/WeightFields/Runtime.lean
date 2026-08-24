import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.WeightFields.Basic

/-! # Fixed polynomial-time formatter for textbook TSP weight fields -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.WeightFields

open PolyBuilder

/-- One fixed polynomial-time TM2 formats an arbitrary adjacency-answer
stream as canonical compact `1`/`2` TSP fields. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id stream := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun answers : List Bool => answers.flatMap body.emit)
  exact boundedLoop_computableInPolyTime body

end CLRS.Chapter34.Turing.TSPReduction.WeightFields
