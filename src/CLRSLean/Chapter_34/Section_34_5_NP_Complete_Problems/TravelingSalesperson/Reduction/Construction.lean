import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Instance
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Instance

/-!
# The textbook HAM-CYCLE to decision-TSP construction

Every graph edge receives weight one and every nonedge receives weight two.
The budget is the number of vertices.
-/

namespace CLRS.Chapter34.TSPReduction

/-- Weight one for a source edge and weight two for a source nonedge. -/
def hamiltonianEdgeWeight (G : HamiltonianCycleInstance)
    (u v : Fin G.vertexCount) : Nat :=
  if G.Adj u v then 1 else 2

/-- The complete weighted graph used in the CLRS HAM-CYCLE-to-TSP reduction. -/
def hamiltonianToTSP (G : HamiltonianCycleInstance) : TSPInstance where
  vertexCount := G.vertexCount
  budget := G.vertexCount
  weight := hamiltonianEdgeWeight G

@[simp] theorem hamiltonianToTSP_vertexCount (G : HamiltonianCycleInstance) :
    (hamiltonianToTSP G).vertexCount = G.vertexCount := rfl

@[simp] theorem hamiltonianToTSP_budget (G : HamiltonianCycleInstance) :
    (hamiltonianToTSP G).budget = G.vertexCount := rfl

theorem hamiltonianToTSP_edgeWeight_of_lt
    (G : HamiltonianCycleInstance) {u v : Nat}
    (hu : u < G.vertexCount) (hv : v < G.vertexCount) :
    (hamiltonianToTSP G).edgeWeight u v =
      if G.Adj u v then 1 else 2 := by
  simp [TSPInstance.edgeWeight, hamiltonianToTSP,
    hamiltonianEdgeWeight, hu, hv]

theorem hamiltonianToTSP_edgeWeight_pos
    (G : HamiltonianCycleInstance) {u v : Nat}
    (hu : u < G.vertexCount) (hv : v < G.vertexCount) :
    0 < (hamiltonianToTSP G).edgeWeight u v := by
  rw [hamiltonianToTSP_edgeWeight_of_lt G hu hv]
  split <;> omega

end CLRS.Chapter34.TSPReduction
