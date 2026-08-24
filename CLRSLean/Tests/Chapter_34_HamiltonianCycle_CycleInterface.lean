import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.CycleInterface

namespace CLRS.Tests.Chapter34HamiltonianCycleCycleInterface

open Chapter34

example (I : CliqueInstance) (vertices : List Nat)
    (hnodup : vertices.Nodup) (hcycle : I.CycleAdjacent vertices)
    (v : Nat) (hv : v ∈ vertices) :
    I.Adj v (vertices.next v hv) :=
  I.adj_next_of_cycleAdjacent hnodup hcycle hv

example (I : CliqueInstance) (vertices : List Nat)
    (hnodup : vertices.Nodup)
    (hlength : vertices.length = I.vertexCount)
    (hbound : ∀ w ∈ vertices, w < I.vertexCount)
    (v : Nat) (hv : v < I.vertexCount) :
    v ∈ vertices :=
  CliqueInstance.mem_of_lt_of_full_cycle_list hnodup hlength hbound hv

#print axioms CliqueInstance.adj_next_of_cycleAdjacent
#print axioms CliqueInstance.next_ne_prev_of_three_le_length
#print axioms CliqueInstance.cycle_neighbors_of_adj_iff_pair

end CLRS.Tests.Chapter34HamiltonianCycleCycleInterface
