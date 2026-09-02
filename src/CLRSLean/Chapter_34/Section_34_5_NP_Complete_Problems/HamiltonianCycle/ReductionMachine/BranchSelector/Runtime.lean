import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchSelector.Semantics

/-!
# VERTEX-COVER to HAM-CYCLE output-selector runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchSelector

open _root_.Turing
open PolyBuilder

/-- A fixed polynomial-time TM2 implements all three output branches. -/
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

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchSelector
