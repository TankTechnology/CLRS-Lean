import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.WeightFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.NormalizedWeights

#check CLRS.Chapter34.Turing.TSPReduction.WeightFields.computableInPolyTime
#check CLRS.Chapter34.Turing.TSPReduction.normalizedWeightFieldsComputableInPolyTime

example :
    CLRS.Chapter34.Turing.TSPReduction.WeightFields.stream
        [true, false, true] =
      CLRS.Chapter34.encodeTSPFields [1, 2, 1] := by
  decide
