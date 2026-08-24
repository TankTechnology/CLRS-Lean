import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.TypedTotal.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchSelector.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.RawWellFormed

/-!
# VERTEX-COVER to HAM-CYCLE: guarded raw target
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.RawTotal

open VertexCover.ComplementMachine

/-- A valid raw source selects the typed candidate; every other source selects
the canonical HAM-CYCLE no-instance. -/
def guardBranch : Bool → Branch
  | true => .ordinary
  | false => .no

/-- Candidate obtained by syntax normalization followed by the total typed
reduction machine. -/
def normalizedTarget (input : List VertexCoverSym) : List HamiltonianCycleSym :=
  TypedTotal.stream (SyntaxNormalizer.normalizedInstanceValue input)

def selectorData (input : List VertexCoverSym) :
    Branch × List HamiltonianCycleSym :=
  (guardBranch (RawWellFormed.rawWellFormedPass input), normalizedTarget input)

/-- Exact all-input map computed by the final fixed reduction machine. -/
def machineVertexCoverToHamiltonianMap
    (input : List VertexCoverSym) : List HamiltonianCycleSym :=
  BranchSelector.selectedOutput (selectorData input)

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.RawTotal
