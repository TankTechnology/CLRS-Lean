import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.NondegeneratePrefix
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorEndpoints.Formatter
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorClique.Formatter

/-!
# VERTEX-COVER to HAM-CYCLE: assembled ordinary target

The machine emits selector-endpoint records in selector-major order.  This is
a permutation of the textbook vertex-major list, so the pair-level instance
below exposes the exact serialization while retaining a precise permutation
bridge to the textbook construction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Ordinary

open HamiltonianCycleReduction

/-- Exact edge order emitted by the assembled fixed machines. -/
def machineClrsEdges (I : VertexCoverInstance) : List (Nat × Nat) :=
  allGlobalWidgetEdges I.edges.length ++
    allIncidenceChainEdges I ++
    SelectorEndpoints.selectorEndpointEdges I ++
    selectorCliqueEdges I.edges.length I.targetSize

/-- Exact nondegenerate instance encoded by the assembled pipeline. -/
def machineClrsInstance (I : VertexCoverInstance) :
    HamiltonianCycleInstance where
  vertexCount := selectorBase I.edges.length + I.targetSize
  targetSize := selectorBase I.edges.length + I.targetSize
  edges := machineClrsEdges I

/-- Header followed by all four edge families. -/
def stream (I : VertexCoverInstance) : List HamiltonianCycleSym :=
  NondegeneratePrefix.stream (encodeVertexCoverInstance I) ++
    Incidence.Chain.chainEdgeStream I ++
    SelectorEndpoints.selectorEndpointStream I ++
    SelectorClique.stream (encodeVertexCoverInstance I)

theorem stream_encode (I : VertexCoverInstance) :
    stream I = encodeHamiltonianCycleInstance (machineClrsInstance I) := by
  rw [stream, NondegeneratePrefix.stream_encode,
    Incidence.Chain.chainEdgeStream_encode,
    SelectorEndpoints.selectorEndpointStream_encode,
    SelectorClique.stream_encode]
  simp [machineClrsInstance, machineClrsEdges, encodeHamiltonianCycleInstance,
    encodeCliqueInstance, List.flatMap_append,
    List.append_assoc]
  rw [prependCliqueTicks_append]
  refine congrArg (fun tail =>
    prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
      (CliqueSym.fieldSep :: tail)) ?_
  exact prependCliqueTicks_append
    (selectorBase I.edges.length + I.targetSize) [CliqueSym.fieldSep] _

/-- Only record order differs from the textbook edge list. -/
theorem machineClrsEdges_perm (I : VertexCoverInstance) :
    List.Perm (machineClrsEdges I) (clrsReductionEdges I) := by
  unfold machineClrsEdges clrsReductionEdges
  exact ((SelectorEndpoints.selectorEndpointEdges_perm I).append_left
    (allGlobalWidgetEdges I.edges.length ++ allIncidenceChainEdges I)).append_right
      (selectorCliqueEdges I.edges.length I.targetSize)

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Ordinary
