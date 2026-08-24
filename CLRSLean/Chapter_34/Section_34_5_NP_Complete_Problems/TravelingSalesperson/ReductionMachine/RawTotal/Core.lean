import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Typed
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawValidity
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawSelector.Core

/-! # Total raw HAM-CYCLE-to-TSP target -/

namespace CLRS.Chapter34.Turing.TSPReduction.RawTotal

open VertexCover.ComplementMachine

def normalizedCandidate (input : List HamiltonianCycleSym) : List TSPSym :=
  Typed.stream (SyntaxNormalizer.normalizedInstanceValue input)

def selectorData (input : List HamiltonianCycleSym) : Bool × List TSPSym :=
  (RawValidity.validPass input, normalizedCandidate input)

/-- Exact all-input map computed by the final fixed machine. -/
def machineMap (input : List HamiltonianCycleSym) : List TSPSym :=
  RawSelector.selectedOutput (selectorData input)

end CLRS.Chapter34.Turing.TSPReduction.RawTotal
