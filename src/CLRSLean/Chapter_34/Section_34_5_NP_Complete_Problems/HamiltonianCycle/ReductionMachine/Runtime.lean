import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.RawTotal.Runtime

/-!
# Public fixed VERTEX-COVER to HAM-CYCLE reduction machine
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine

open _root_.Turing

/-- A fixed polynomial-time TM2 computes the all-input guarded HAM-CYCLE
reduction map from raw VERTEX-COVER words. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id
      RawTotal.machineVertexCoverToHamiltonianMap :=
  RawTotal.computableInPolyTime

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine
