import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.PairOrderProperties

/-! # Symmetry semantics of a well-formed TSP matrix -/

namespace CLRS.Chapter34

private theorem firstOrientations_map_pairOrientations
    (pairs : List (Nat × Nat)) (weight : Nat × Nat → Nat) :
    TSPData.firstOrientations
        ((pairs.flatMap tspPairOrientations).map weight) =
      pairs.map weight := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨u, v⟩
      simp [tspPairOrientations, TSPData.firstOrientations, ih]

private theorem secondOrientations_map_pairOrientations
    (pairs : List (Nat × Nat)) (weight : Nat × Nat → Nat) :
    TSPData.secondOrientations
        ((pairs.flatMap tspPairOrientations).map weight) =
      pairs.map fun pair => weight (pair.2, pair.1) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨u, v⟩
      simp [tspPairOrientations, TSPData.secondOrientations, ih]

private theorem map_eq_map_at_mem {α β : Type}
    (values : List α) (left right : α → β)
    (heq : values.map left = values.map right) {value : α}
    (hmem : value ∈ values) : left value = right value := by
  induction values with
  | nil => simp at hmem
  | cons head values ih =>
      simp only [List.map_cons, List.cons.injEq] at heq
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact heq.1
      · exact ih heq.2 htail

private theorem lookup_symmetric_of_orientationPairsEqual
    (data : TSPData)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount)
    (hsymmetric : TSPData.OrientationPairsEqual
      (data.weights.drop data.vertexCount))
    {u v : Nat} (hu : u < data.vertexCount)
    (hv : v < data.vertexCount) :
    lookupTSPWeight (tspPairOrder data.vertexCount) data.weights u v =
      lookupTSPWeight (tspPairOrder data.vertexCount) data.weights v u := by
  let weight : Nat × Nat → Nat := fun pair =>
    lookupTSPWeight (tspPairOrder data.vertexCount) data.weights
      pair.1 pair.2
  have hweights := tspWeights_eq_map_lookup data hshape
  have htail : data.weights.drop data.vertexCount =
      ((tspNormalizedPairs data.vertexCount).flatMap
        tspPairOrientations).map weight := by
    rw [hweights]
    simp [tspPairOrder, weight]
  have horientations : TSPData.OrientationPairsEqual
      (((tspNormalizedPairs data.vertexCount).flatMap
        tspPairOrientations).map weight) := by
    rw [← htail]
    exact hsymmetric
  have hmapped :
      (tspNormalizedPairs data.vertexCount).map weight =
        (tspNormalizedPairs data.vertexCount).map fun pair =>
          weight (pair.2, pair.1) := by
    have heq := (TSPData.orientationPairsEqual_iff _).mp horientations
    rw [firstOrientations_map_pairOrientations,
      secondOrientations_map_pairOrientations] at heq
    exact heq
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exact map_eq_map_at_mem _ _ _ hmapped
      (mem_tspNormalizedPairs_iff.mpr ⟨huv, hv⟩)
  · rfl
  · exact (map_eq_map_at_mem _ _ _ hmapped
      (mem_tspNormalizedPairs_iff.mpr ⟨hvu, hu⟩)).symm

/-- `TSPData.WellFormed` is not merely a serialization condition: its paired
orientation clause makes the interpreted complete graph symmetric. -/
theorem TSPData.toInstance_edgeWeight_comm (data : TSPData)
    (hwellFormed : data.WellFormed) {u v : Nat}
    (hu : u < data.vertexCount) (hv : v < data.vertexCount) :
    data.toInstance.edgeWeight u v = data.toInstance.edgeWeight v u := by
  rw [TSPInstance.edgeWeight_of_lt _ hu hv,
    TSPInstance.edgeWeight_of_lt _ hv hu]
  exact lookup_symmetric_of_orientationPairsEqual data
    hwellFormed.1 hwellFormed.2 hu hv

end CLRS.Chapter34
