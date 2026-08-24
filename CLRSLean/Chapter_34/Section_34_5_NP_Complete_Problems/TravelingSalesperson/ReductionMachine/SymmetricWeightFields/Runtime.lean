import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.SymmetricWeightFields.Basic

/-! # Fixed polynomial-time formatter for symmetric TSP pair fields -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.SymmetricWeightFields

open PolyBuilder

noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id stream := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun answers : List Bool => answers.flatMap body.emit)
  exact boundedLoop_computableInPolyTime body

end CLRS.Chapter34.Turing.TSPReduction.SymmetricWeightFields
