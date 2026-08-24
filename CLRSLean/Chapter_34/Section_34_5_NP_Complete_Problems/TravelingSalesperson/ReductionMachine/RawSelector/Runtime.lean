import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawSelector.Semantics

/-! # Guarded TSP output selector: fixed runtime -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.RawSelector

open _root_.Turing
open PolyBuilder

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding id selectedOutput := by
  let machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun (inputEncoding input)
        have hstream := stream_inputEncoding input
        unfold stream at hstream
        rw [hstream] at output
        simpa using output }

end CLRS.Chapter34.Turing.TSPReduction.RawSelector
