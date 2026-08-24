import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Reduction
import Mathlib.Tactic

/-!
# Serialized HAM-CYCLE to decision-TSP construction

This file materializes the typed textbook weight function as a proof-free,
row-major list suitable for the honest TSP encoder.
-/

namespace CLRS.Chapter34.TSPReduction

/-- The textbook complete weight matrix, listed in row-major order. -/
def hamiltonianWeights (G : HamiltonianCycleInstance) : List Nat :=
  List.ofFn fun index : Fin (G.vertexCount * G.vertexCount) =>
    (hamiltonianToTSP G).edgeWeight
      (index.val / G.vertexCount) (index.val % G.vertexCount)

@[simp] theorem hamiltonianWeights_length (G : HamiltonianCycleInstance) :
    (hamiltonianWeights G).length = G.vertexCount * G.vertexCount := by
  simp [hamiltonianWeights]

/-- Proof-free row-major data emitted by the serialized reduction. -/
def hamiltonianTSPData (G : HamiltonianCycleInstance) : TSPData where
  vertexCount := G.vertexCount
  budget := G.vertexCount
  weights := hamiltonianWeights G

@[simp] theorem hamiltonianTSPData_wellFormed
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).WellFormed := by
  simp [TSPData.WellFormed, hamiltonianTSPData]

private theorem rowMajor_index_lt (G : HamiltonianCycleInstance)
    (u v : Fin G.vertexCount) :
    u.val * G.vertexCount + v.val <
      G.vertexCount * G.vertexCount := by
  nlinarith [u.isLt, v.isLt]

/-- Row-major interpretation recovers the existing typed textbook
construction exactly. -/
theorem hamiltonianTSPData_toInstance
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).toInstance = hamiltonianToTSP G := by
  rw [TSPInstance.mk.injEq]
  refine ⟨rfl, rfl, heq_of_eq ?_⟩
  change
    (fun (u v : Fin G.vertexCount) =>
      (hamiltonianWeights G).getD
        (u.val * G.vertexCount + v.val) 0) =
      (hamiltonianToTSP G).weight
  funext u v
  ·
    have hindex := rowMajor_index_lt G u v
    have hindex' : u.val * G.vertexCount + v.val <
        (hamiltonianWeights G).length := by
      simpa using hindex
    have hlookup :
        (hamiltonianWeights G).getD
            (u.val * G.vertexCount + v.val) 0 =
          (hamiltonianToTSP G).edgeWeight
            ((u.val * G.vertexCount + v.val) / G.vertexCount)
            ((u.val * G.vertexCount + v.val) % G.vertexCount) := by
      simp [hamiltonianWeights, hindex]
    rw [hlookup]
    have hpositive : 0 < G.vertexCount := Nat.zero_lt_of_lt u.isLt
    have hdiv :
        (u.val * G.vertexCount + v.val) / G.vertexCount = u.val := by
      rw [Nat.mul_comm u.val G.vertexCount,
        Nat.mul_add_div hpositive u.val v.val]
      simp [Nat.div_eq_of_lt v.isLt]
    have hmod :
        (u.val * G.vertexCount + v.val) % G.vertexCount = v.val := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt v.isLt]
    simp [hdiv, hmod, TSPInstance.edgeWeight, u.isLt, v.isLt]

/-- The proof-free record has precisely the typed reduction semantics. -/
theorem hamiltonianTSPData_hasTour_iff
    (G : HamiltonianCycleInstance) :
    (hamiltonianTSPData G).HasTour ↔ G.HasHamiltonianCycle := by
  rw [TSPData.HasTour]
  simp only [hamiltonianTSPData_wellFormed, true_and]
  rw [hamiltonianTSPData_toInstance, hamiltonianToTSP_correct]

end CLRS.Chapter34.TSPReduction
