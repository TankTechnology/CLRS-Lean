import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.RawReduction.Construction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.NormalizedWeights

/-!
# HAM-CYCLE to TSP machine: complete weight semantics

The fixed graph lookup naturally produces one weight per normalized undirected
pair.  This file proves that prefixing the diagonal weights and duplicating
each pair weight gives exactly the complete directed matrix expected by the
honest TSP encoding.
-/

namespace CLRS.Chapter34.Turing.TSPReduction

theorem tspNormalizedPairs_eq_vertexCoverNormalizedPairs (n : Nat) :
    tspNormalizedPairs n = vertexCoverNormalizedPairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tspNormalizedPairs, vertexCoverNormalizedPairs, ih]

/-- Complete symmetric matrix assembled from the reusable normalized-pair
weight stream. -/
def completeHamiltonianWeights (I : CliqueInstance) : List Nat :=
  List.replicate I.vertexCount 2 ++
    (normalizedPairWeights I).flatMap fun weight => [weight, weight]

private theorem diagonalWeights_eq (I : CliqueInstance) :
    ((List.range I.vertexCount).map fun vertex => (vertex, vertex)).map
        (fun pair =>
          (CLRS.Chapter34.TSPReduction.hamiltonianToTSP I).edgeWeight
            pair.1 pair.2) =
      List.replicate I.vertexCount 2 := by
  rw [List.map_map]
  have mapped :
      (List.range I.vertexCount).map
          ((fun pair =>
            (CLRS.Chapter34.TSPReduction.hamiltonianToTSP I).edgeWeight
              pair.1 pair.2) ∘ fun vertex => (vertex, vertex)) =
        List.replicate (List.range I.vertexCount).length 2 := by
    apply List.map_eq_replicate_iff.mpr
    intro vertex hvertex
    have hlt := List.mem_range.mp hvertex
    change
      (CLRS.Chapter34.TSPReduction.hamiltonianToTSP I).edgeWeight
        vertex vertex = 2
    rw [CLRS.Chapter34.TSPReduction.hamiltonianToTSP_edgeWeight_of_lt I hlt hlt]
    simp [CliqueInstance.not_adj_self]
  simpa using mapped

private theorem orientationWeights_eq (I : CliqueInstance)
    {pair : Nat × Nat} (hpair : pair ∈ tspNormalizedPairs I.vertexCount) :
    (tspPairOrientations pair).map
        (fun endpoints =>
          (CLRS.Chapter34.TSPReduction.hamiltonianToTSP I).edgeWeight
            endpoints.1 endpoints.2) =
      let weight := if pair ∈ I.edges then 1 else 2
      [weight, weight] := by
  rcases pair with ⟨u, v⟩
  have hpairs := mem_tspNormalizedPairs_iff.mp hpair
  have huv : u < v := hpairs.1
  have hu : u < I.vertexCount := huv.trans hpairs.2
  have hv : v < I.vertexCount := hpairs.2
  rw [show tspPairOrientations (u, v) = [(u, v), (v, u)] by rfl]
  simp only [List.map_cons, List.map_nil]
  rw [CLRS.Chapter34.TSPReduction.hamiltonianToTSP_edgeWeight_of_lt I hu hv,
    CLRS.Chapter34.TSPReduction.hamiltonianToTSP_edgeWeight_of_lt I hv hu]
  simp [CliqueInstance.Adj, huv,
    Nat.not_lt.mpr (Nat.le_of_lt huv)]

private theorem orientedPairWeights_eq (I : CliqueInstance) :
    ((tspNormalizedPairs I.vertexCount).flatMap tspPairOrientations).map
        (fun pair =>
          (CLRS.Chapter34.TSPReduction.hamiltonianToTSP I).edgeWeight
            pair.1 pair.2) =
      (normalizedPairWeights I).flatMap fun weight => [weight, weight] := by
  rw [List.map_flatMap]
  unfold normalizedPairWeights
  simp only [VertexCover.ComplementMachine.NonedgeFilter.candidatePairs,
    ← tspNormalizedPairs_eq_vertexCoverNormalizedPairs, List.flatMap_map]
  apply List.flatMap_congr
  intro pair hpair
  exact orientationWeights_eq I hpair

theorem completeHamiltonianWeights_eq (I : CliqueInstance) :
    completeHamiltonianWeights I =
      CLRS.Chapter34.TSPReduction.hamiltonianWeights I := by
  rw [CLRS.Chapter34.TSPReduction.hamiltonianWeights, tspPairOrder,
    List.map_append]
  rw [diagonalWeights_eq, orientedPairWeights_eq]
  rfl

end CLRS.Chapter34.Turing.TSPReduction
