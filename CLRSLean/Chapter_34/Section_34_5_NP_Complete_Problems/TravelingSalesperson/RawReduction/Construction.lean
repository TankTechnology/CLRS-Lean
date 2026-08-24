import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Reduction
import Mathlib.Tactic

/-!
# Serialized HAM-CYCLE to decision-TSP construction

This file materializes the typed textbook weight function as a proof-free
complete-matrix list suitable for the honest TSP encoder.
-/

namespace CLRS.Chapter34.TSPReduction

/-- The textbook complete weight matrix, listed in canonical complete-pair
order. -/
def hamiltonianWeights (G : HamiltonianCycleInstance) : List Nat :=
  (tspPairOrder G.vertexCount).map fun pair =>
    (hamiltonianToTSP G).edgeWeight pair.1 pair.2

@[simp] theorem hamiltonianWeights_length (G : HamiltonianCycleInstance) :
    (hamiltonianWeights G).length = G.vertexCount * G.vertexCount := by
  simp [hamiltonianWeights]

/-- Proof-free complete-matrix data emitted by the serialized reduction. -/
def hamiltonianTSPData (G : HamiltonianCycleInstance) : TSPData where
  vertexCount := G.vertexCount
  budget := G.vertexCount
  weights := hamiltonianWeights G

@[simp] theorem hamiltonianTSPData_wellFormed
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).WellFormed := by
  simp [TSPData.WellFormed, hamiltonianTSPData]

/-- Complete-pair interpretation recovers the existing typed textbook
construction exactly. -/
theorem hamiltonianTSPData_toInstance
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).toInstance = hamiltonianToTSP G := by
  rw [TSPInstance.mk.injEq]
  refine ⟨rfl, rfl, heq_of_eq ?_⟩
  change
    (fun (u v : Fin G.vertexCount) =>
      lookupTSPWeight (tspPairOrder G.vertexCount)
        (hamiltonianWeights G) u.val v.val) =
      (hamiltonianToTSP G).weight
  funext u v
  change lookupTSPWeight (tspPairOrder G.vertexCount)
      ((tspPairOrder G.vertexCount).map fun pair =>
        (hamiltonianToTSP G).edgeWeight pair.1 pair.2)
      u.val v.val = _
  rw [lookupTSPWeight_map_of_mem _ _
    (mem_tspPairOrder_iff.mpr ⟨u.isLt, v.isLt⟩)]
  rw [TSPInstance.edgeWeight_of_lt _ u.isLt v.isLt]
  congr 1

/-- The proof-free record has precisely the typed reduction semantics. -/
theorem hamiltonianTSPData_hasTour_iff
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).HasTour ↔ G.HasHamiltonianCycle := by
  rw [TSPData.HasTour]
  simp only [hamiltonianTSPData_wellFormed, true_and]
  rw [hamiltonianTSPData_toInstance, hamiltonianToTSP_correct]

end CLRS.Chapter34.TSPReduction
