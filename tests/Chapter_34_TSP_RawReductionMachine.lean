import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawTotal

open CLRS Chapter34
open _root_.Turing

noncomputable section

example : TM2ComputableInPolyTime id id
    CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP :=
  CLRS.Chapter34.Turing.TSPReduction.RawTotal.computableInPolyTime

example (input : List HamiltonianCycleSym) :
    CLRS.Chapter34.Turing.TSPReduction.RawTotal.machineMap input =
      CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP input :=
  CLRS.Chapter34.Turing.TSPReduction.RawTotal.machineMap_eq_rawHamiltonianToTSP
    input

#print axioms CLRS.Chapter34.Turing.TSPReduction.RawValidity.validPass_eq_true_iff
#print axioms CLRS.Chapter34.Turing.TSPReduction.RawTotal.machineMap_eq_rawHamiltonianToTSP
#print axioms CLRS.Chapter34.Turing.TSPReduction.RawTotal.computableInPolyTime
