import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.RawReduction.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.Length
import Mathlib.Tactic

/-! # Physical output bound of the serialized HAM-CYCLE to TSP map -/

namespace CLRS.Chapter34.TSPReduction

theorem hamiltonianWeights_lt_three (G : HamiltonianCycleInstance) :
    ∀ weight ∈ hamiltonianWeights G, weight < 3 := by
  intro weight hweight
  simp only [hamiltonianWeights, List.mem_ofFn] at hweight
  rcases hweight with ⟨index, rfl⟩
  simp only [TSPInstance.edgeWeight, hamiltonianToTSP,
    hamiltonianEdgeWeight]
  split <;> try omega
  split <;> try omega
  split <;> omega

/-- The encoded typed construction is quadratically bounded by its vertex
count, with a deliberately simple uniform constant. -/
theorem encode_hamiltonianTSPData_length_le
    (G : HamiltonianCycleInstance) :
    (encodeTSPData (hamiltonianTSPData G)).length ≤
      5 * G.vertexCount ^ 2 + 2 * G.vertexCount + 8 := by
  have hweights := encodeTSPFields_length_le_of_lt
    (hamiltonianWeights_lt_three G)
  have hvertex : (encodeTSPField G.vertexCount).length ≤
      G.vertexCount + 3 := by
    exact encodeTSPField_length_le_of_lt (Nat.lt_succ_self _)
  rw [encodeTSPData_length]
  change (List.flatMap encodeTSPField (G.vertexCount ::
      G.vertexCount :: hamiltonianWeights G)).length + 2 ≤ _
  change (List.flatMap encodeTSPField (hamiltonianWeights G)).length ≤
    (hamiltonianWeights G).length * (3 + 2) at hweights
  simp only [List.flatMap_cons, List.length_append,
    hamiltonianWeights_length] at hweights ⊢
  nlinarith

/-- The total raw map has a uniform quadratic physical output bound on every
source word, including malformed inputs. -/
theorem rawHamiltonianToTSP_length_le
    (input : List HamiltonianCycleSym) :
    (rawHamiltonianToTSP input).length ≤
      10 * (input.length + 1) ^ 2 := by
  generalize hdecode : decodeHamiltonianCycleInstance input = result
  cases result with
  | none => simp [rawHamiltonianToTSP, hdecode]
  | some G =>
      by_cases hvalid : G.WellFormed ∧ G.targetSize = G.vertexCount
      · have hsource := decodeCliqueInstance_fields_le_length hdecode
        have houtput := encode_hamiltonianTSPData_length_le G
        rw [show rawHamiltonianToTSP input =
            encodeTSPData (hamiltonianTSPData G) by
          simp [rawHamiltonianToTSP, hdecode, hvalid]]
        nlinarith
      · simp [rawHamiltonianToTSP, hdecode, hvalid]

end CLRS.Chapter34.TSPReduction
