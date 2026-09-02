import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchClassifier.Semantics

/-!
# VERTEX-COVER to HAM-CYCLE branch-classifier runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchClassifier

open _root_.Turing
open PolyBuilder

/-- A fixed polynomial-time TM2 classifies the typed total reduction branch. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id
      (fun I : VertexCoverInstance => [(branch I).symbol]) := by
  let machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun (encodeVertexCoverInstance I)
        have hstream := stream_encode I
        unfold stream at hstream
        rw [hstream] at output
        simpa using output }

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchClassifier
