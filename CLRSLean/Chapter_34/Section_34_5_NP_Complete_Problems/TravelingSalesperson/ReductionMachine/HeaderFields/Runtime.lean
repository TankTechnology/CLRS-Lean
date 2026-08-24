import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.HeaderFields.Basic

/-! # Fixed polynomial-time TSP header formatters -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.HeaderFields

open PolyBuilder

noncomputable def firstComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id first :=
  statefulFlatMap_computableInPolyTime firstSpec

noncomputable def secondComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id second :=
  statefulFlatMap_computableInPolyTime secondSpec

end CLRS.Chapter34.Turing.TSPReduction.HeaderFields
