import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Ordinary.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchSelector.Core

/-!
# VERTEX-COVER to HAM-CYCLE: exact total typed target
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.TypedTotal

open HamiltonianCycleReduction

/-- Exact typed instance serialized by the fixed machine. -/
def machineInstance (I : VertexCoverInstance) : HamiltonianCycleInstance :=
  match branch I with
  | .ordinary => Ordinary.machineClrsInstance I
  | .yes => canonicalHamiltonianYesInstance
  | .no => canonicalHamiltonianNoInstance

def selectorData (I : VertexCoverInstance) : Branch × List CliqueSym :=
  (branch I, Ordinary.stream I)

/-- Exact total output stream before the later raw syntax guard. -/
def stream (I : VertexCoverInstance) : List CliqueSym :=
  BranchSelector.selectedOutput (selectorData I)

theorem stream_encode (I : VertexCoverInstance) :
    stream I = encodeHamiltonianCycleInstance (machineInstance I) := by
  cases hbranch : branch I <;>
    simp [stream, selectorData, BranchSelector.selectedOutput, machineInstance,
      hbranch, Ordinary.stream_encode]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.TypedTotal
