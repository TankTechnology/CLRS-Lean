import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SelectedWeightSum
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.CostSemantics.CyclePairs
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Symmetry

/-! # Selected matrix weights equal twice the symmetric tour cost -/

namespace CLRS.Chapter34.Turing.TSPVerifier.CostSemantics

open PolyBuilder
open HamiltonianCycle.VerifierMachine.CyclePairs
open GeneralCliqueVerifier.QueryNormalizer
open SelectedWeightSum

def normalizedTourEdges (vertices : List Nat) : List (Nat × Nat) :=
  (cyclePairs vertices).map normalizeQuery

def matrixFlags (vertexCount : Nat) (vertices : List Nat) : List Bool :=
  List.replicate vertexCount false ++
    (tspNormalizedPairs vertexCount).flatMap fun pair =>
      let selected := decide (pair ∈ normalizedTourEdges vertices)
      [selected, selected]

def selectedMatrixPairs (vertexCount : Nat) (vertices : List Nat) :
    List (Nat × Nat) :=
  selectListByBool (matrixFlags vertexCount vertices)
    (tspPairOrder vertexCount)

theorem selectedMatrixPairs_eq (vertexCount : Nat)
    (vertices : List Nat) :
    selectedMatrixPairs vertexCount vertices =
      ((tspNormalizedPairs vertexCount).filter fun pair =>
        pair ∈ normalizedTourEdges vertices).flatMap tspPairOrientations := by
  rw [selectedMatrixPairs, matrixFlags, tspPairOrder,
    selectListByBool_append]
  · simp only [selectListByBool_replicate_false, List.nil_append]
    rw [selectListByBool_flatMap]
    · have hflatten (pairs : List (Nat × Nat)) :
          (pairs.map (fun pair =>
              selectListByBool
                [decide (pair ∈ normalizedTourEdges vertices),
                  decide (pair ∈ normalizedTourEdges vertices)]
                (tspPairOrientations pair))).flatten =
            ((pairs.filter fun pair =>
              pair ∈ normalizedTourEdges vertices).map
                tspPairOrientations).flatten := by
        induction pairs with
        | nil => rfl
        | cons pair pairs ih =>
            simp only [List.map_cons, List.flatten_cons, List.filter_cons]
            by_cases hselected : pair ∈ normalizedTourEdges vertices
            · have hdecide : decide
                  (pair ∈ normalizedTourEdges vertices) = true :=
                decide_eq_true hselected
              rw [hdecide]
              simp only [↓reduceIte, List.map_cons,
                List.flatten_cons]
              have hhead : selectListByBool [true, true]
                  (tspPairOrientations pair) = tspPairOrientations pair := by
                rcases pair with ⟨left, right⟩
                rfl
              rw [hhead, ih]
            · have hdecide : decide
                  (pair ∈ normalizedTourEdges vertices) = false :=
                decide_eq_false hselected
              rw [hdecide]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have hhead : selectListByBool [false, false]
                  (tspPairOrientations pair) = [] := by
                rcases pair with ⟨left, right⟩
                rfl
              rw [hhead, List.nil_append]
              exact ih
      exact hflatten _
    · intro pair hpair
      rfl
  · simp

private theorem weights_eq_map_edgeWeight (data : TSPData)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    data.weights = (tspPairOrder data.vertexCount).map fun pair =>
      data.toInstance.edgeWeight pair.1 pair.2 := by
  rw [tspWeights_eq_map_lookup data hshape]
  apply List.map_congr_left
  intro pair hpair
  have hbounds := mem_tspPairOrder_iff.mp hpair
  rw [TSPInstance.edgeWeight_of_lt _ hbounds.1 hbounds.2]
  rfl

theorem selectedValues_eq_selectedMatrixPairs (vertices : List Nat)
    (data : TSPData)
    (hshape : data.weights.length = data.vertexCount * data.vertexCount) :
    selectedValues (matrixFlags data.vertexCount vertices) data.weights =
      (selectedMatrixPairs data.vertexCount vertices).map fun pair =>
        data.toInstance.edgeWeight pair.1 pair.2 := by
  rw [weights_eq_map_edgeWeight data hshape]
  change selectListByBool (matrixFlags data.vertexCount vertices)
      ((tspPairOrder data.vertexCount).map fun pair =>
        data.toInstance.edgeWeight pair.1 pair.2) = _
  rw [selectListByBool_map]
  rfl

private theorem normalizedTourEdge_mem (vertices : List Nat)
    (data : TSPData)
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup)
    (hbound : ∀ vertex ∈ vertices, vertex < data.vertexCount)
    {pair : Nat × Nat} (hpair : pair ∈ normalizedTourEdges vertices) :
    pair ∈ tspNormalizedPairs data.vertexCount := by
  rcases List.mem_map.mp hpair with ⟨edge, hedge, rfl⟩
  have hendpoints := cyclePairs_endpoints_mem hedge
  have hne := cyclePairs_endpoints_ne hthree hnodup hedge
  have hleft := hbound edge.1 hendpoints.1
  have hright := hbound edge.2 hendpoints.2
  rcases edge with ⟨left, right⟩
  by_cases hle : left ≤ right
  · have hlt : left < right := Nat.lt_of_le_of_ne hle hne
    simpa [normalizeQuery, hle] using
      (mem_tspNormalizedPairs_iff.mpr ⟨hlt, hright⟩)
  · have hlt : right < left := Nat.lt_of_not_ge hle
    simpa [normalizeQuery, hle] using
      (mem_tspNormalizedPairs_iff.mpr ⟨hlt, hleft⟩)

private theorem selectedNormalizedPairs_perm (vertices : List Nat)
    (data : TSPData)
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup)
    (hbound : ∀ vertex ∈ vertices, vertex < data.vertexCount) :
    ((tspNormalizedPairs data.vertexCount).filter fun pair =>
        pair ∈ normalizedTourEdges vertices).Perm
      (normalizedTourEdges vertices) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (tspNormalizedPairs_nodup _).filter _
  · exact normalizedCyclePairs_nodup vertices hthree hnodup
  · apply Finset.ext
    intro pair
    simp only [List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨_, hselected⟩
      exact of_decide_eq_true hselected
    · intro hpair
      exact ⟨normalizedTourEdge_mem vertices data hthree hnodup
        hbound hpair, decide_eq_true hpair⟩

private theorem orientations_weight_sum (pairs : List (Nat × Nat))
    (data : TSPData) (hwellFormed : data.WellFormed)
    (hbounds : ∀ pair ∈ pairs,
      pair.1 < data.vertexCount ∧ pair.2 < data.vertexCount) :
    ((pairs.flatMap tspPairOrientations).map fun pair =>
        data.toInstance.edgeWeight pair.1 pair.2).sum =
      2 * (pairs.map fun pair =>
        data.toInstance.edgeWeight pair.1 pair.2).sum := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      have hpairBounds := hbounds pair (by simp)
      have hcomm := data.toInstance_edgeWeight_comm hwellFormed
        hpairBounds.1 hpairBounds.2
      have htail : ∀ next ∈ pairs,
          next.1 < data.vertexCount ∧ next.2 < data.vertexCount := by
        intro next hnext
        exact hbounds next (by simp [hnext])
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        ih htail]
      simp [tspPairOrientations, hcomm, Nat.mul_add, Nat.add_assoc]
      omega

private theorem normalizedTourWeight_sum (vertices : List Nat)
    (data : TSPData) (hwellFormed : data.WellFormed)
    (hbound : ∀ vertex ∈ vertices, vertex < data.vertexCount) :
    ((normalizedTourEdges vertices).map fun pair =>
        data.toInstance.edgeWeight pair.1 pair.2).sum =
      data.toInstance.tourCost vertices := by
  rw [normalizedTourEdges]
  rw [← cyclePairs_weight_sum data.toInstance vertices]
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro pair hpair
  have hendpoints := cyclePairs_endpoints_mem hpair
  have hleft := hbound pair.1 hendpoints.1
  have hright := hbound pair.2 hendpoints.2
  by_cases hle : pair.1 ≤ pair.2
  · simp [normalizeQuery, hle]
  · simp only [Function.comp_def, normalizeQuery, hle, ↓reduceIte]
    exact (data.toInstance_edgeWeight_comm hwellFormed hleft hright).symm

/-- Under the certificate conditions checked by the other verifier branches,
the matrix selector retains both orientations of every tour edge; symmetry
therefore makes its numeric sum exactly twice the textbook tour cost. -/
theorem selectedValues_sum_eq_two_mul_tourCost (vertices : List Nat)
    (data : TSPData) (hwellFormed : data.WellFormed)
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup)
    (hbound : ∀ vertex ∈ vertices, vertex < data.vertexCount) :
    (selectedValues (matrixFlags data.vertexCount vertices)
        data.weights).sum =
      2 * data.toInstance.tourCost vertices := by
  rw [selectedValues_eq_selectedMatrixPairs vertices data hwellFormed.1,
    selectedMatrixPairs_eq]
  let selectedPairs :=
    (tspNormalizedPairs data.vertexCount).filter fun pair =>
      pair ∈ normalizedTourEdges vertices
  have hselectedBounds : ∀ pair ∈ selectedPairs,
      pair.1 < data.vertexCount ∧ pair.2 < data.vertexCount := by
    intro pair hpair
    have hnormalized := (List.mem_filter.mp hpair).1
    have hbounds := mem_tspNormalizedPairs_iff.mp hnormalized
    exact ⟨hbounds.1.trans hbounds.2, hbounds.2⟩
  rw [orientations_weight_sum selectedPairs data hwellFormed
    hselectedBounds]
  have hperm := selectedNormalizedPairs_perm vertices data hthree
    hnodup hbound
  have hsum := (hperm.map fun pair =>
    data.toInstance.edgeWeight pair.1 pair.2).sum_nat
  rw [hsum, normalizedTourWeight_sum vertices data hwellFormed hbound]

/-- Numeric semantics of the full concrete selected-field summation machine
on canonical inputs. -/
theorem binaryNatValue_selectedSumBits_encode_eq (vertices : List Nat)
    (data : TSPData) (hwellFormed : data.WellFormed)
    (hthree : 3 ≤ vertices.length) (hnodup : vertices.Nodup)
    (hcount : vertices.length = data.vertexCount)
    (hbound : ∀ vertex ∈ vertices, vertex < data.vertexCount) :
    binaryNatValue
        (SelectedWeightSum.selectedSumBits
          (UnaryCertificate.encode vertices, encodeTSPData data)) =
      2 * data.toInstance.tourCost vertices := by
  rw [SelectedWeightSum.binaryNatValue_selectedSumBits_encode]
  have hflags :
      List.replicate vertices.length false ++
          ((vertexCoverNormalizedPairs vertices.length).map fun edge =>
            decide (edge ∈
              (cyclePairs vertices).map normalizeQuery)).flatMap
                (fun flag => [flag, flag]) =
        matrixFlags data.vertexCount vertices := by
    simp [matrixFlags, normalizedTourEdges, hcount,
      tspNormalizedPairs_eq_vertexCoverNormalizedPairs, List.flatMap_map]
    rfl
  rw [hflags]
  exact selectedValues_sum_eq_two_mul_tourCost vertices data hwellFormed
    hthree hnodup hbound

end CLRS.Chapter34.Turing.TSPVerifier.CostSemantics
