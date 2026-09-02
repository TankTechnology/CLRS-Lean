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

private theorem orientationPairsEqual_orientations
    (pairs : List (Nat × Nat)) (weight : Nat × Nat → Nat)
    (hsymmetric : ∀ pair ∈ pairs,
      weight pair = weight (pair.2, pair.1)) :
    TSPData.OrientationPairsEqual
      ((pairs.flatMap tspPairOrientations).map weight) := by
  induction pairs with
  | nil => trivial
  | cons pair pairs ih =>
      rw [List.flatMap_cons, List.map_append]
      rcases pair with ⟨u, v⟩
      simp only [tspPairOrientations, List.map_cons, List.map_nil]
      exact ⟨hsymmetric (u, v) (by simp), ih (by
        intro pair hpair
        exact hsymmetric pair (by simp [hpair]))⟩

private theorem hamiltonianWeights_symmetric
    (G : HamiltonianCycleInstance) :
    TSPData.OrientationPairsEqual
      ((hamiltonianWeights G).drop G.vertexCount) := by
  let weight : Nat × Nat → Nat := fun pair =>
    (hamiltonianToTSP G).edgeWeight pair.1 pair.2
  have hsymmetric : ∀ pair ∈ tspNormalizedPairs G.vertexCount,
      weight pair = weight (pair.2, pair.1) := by
    rintro ⟨u, v⟩ hpair
    have hpairs := mem_tspNormalizedPairs_iff.mp hpair
    have hu : u < G.vertexCount := hpairs.1.trans hpairs.2
    have hv : v < G.vertexCount := hpairs.2
    dsimp only [weight]
    rw [hamiltonianToTSP_edgeWeight_of_lt G hu hv,
      hamiltonianToTSP_edgeWeight_of_lt G hv hu]
    apply if_congr
    · exact G.adj_comm u v
    · rfl
    · rfl
  have horientations := orientationPairsEqual_orientations
    (tspNormalizedPairs G.vertexCount) weight hsymmetric
  simpa [hamiltonianWeights, tspPairOrder, weight] using horientations

@[simp] theorem hamiltonianTSPData_wellFormed
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).WellFormed := by
  exact ⟨by simp [hamiltonianTSPData], hamiltonianWeights_symmetric G⟩

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
