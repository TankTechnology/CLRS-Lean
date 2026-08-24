import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.RawReduction.Construction

/-! # Total serialized HAM-CYCLE to decision-TSP map -/

namespace CLRS.Chapter34.TSPReduction

/-- Total raw reduction.  A canonical, well-formed graph-only HAM instance is
mapped to its canonical 1/2-weight matrix; every malformed source is sent to a
fixed rejected TSP word. -/
def rawHamiltonianToTSP
    (input : List HamiltonianCycleSym) : List TSPSym :=
  match decodeHamiltonianCycleInstance input with
  | some G =>
      if G.WellFormed ∧ G.targetSize = G.vertexCount then
        encodeTSPData (hamiltonianTSPData G)
      else []
  | none => []

@[simp] theorem rawHamiltonianToTSP_encode
    (G : HamiltonianCycleInstance) (hwellFormed : G.WellFormed)
    (htarget : G.targetSize = G.vertexCount) :
    rawHamiltonianToTSP (encodeHamiltonianCycleInstance G) =
      encodeTSPData (hamiltonianTSPData G) := by
  simp only [rawHamiltonianToTSP]
  rw [show decodeHamiltonianCycleInstance
      (encodeHamiltonianCycleInstance G) = some G from
    decode_encodeCliqueInstance G]
  simp [hwellFormed, htarget]

/-- Exact language equivalence of the total serialized textbook map. -/
theorem rawHamiltonianToTSP_correct (input : List HamiltonianCycleSym) :
    input ∈ GeneralHAMCYCLE ↔
      rawHamiltonianToTSP input ∈ GeneralTSP := by
  have hempty : ([] : List TSPSym) ∉ GeneralTSP := by
    rintro ⟨data, hdecodeData, _⟩
    simp [decodeTSPData] at hdecodeData
  generalize hdecode : decodeHamiltonianCycleInstance input = result
  cases result with
  | none =>
      have hsource : input ∉ GeneralHAMCYCLE := by
        rintro ⟨G, hG, _⟩
        rw [hdecode] at hG
        contradiction
      rw [show rawHamiltonianToTSP input = [] by
        simp [rawHamiltonianToTSP, hdecode]]
      exact iff_of_false hsource hempty
  | some G =>
      by_cases hvalid : G.WellFormed ∧ G.targetSize = G.vertexCount
      · have hsource : input ∈ GeneralHAMCYCLE ↔
            G.HasHamiltonianCycle := by
          constructor
          · rintro ⟨decoded, hdecoded, _, _, hcycle⟩
            have hG : G = decoded := Option.some.inj
              (hdecode.symm.trans hdecoded)
            simpa [hG] using hcycle
          · intro hcycle
            exact ⟨G, hdecode, hvalid.1, hvalid.2, hcycle⟩
        rw [show rawHamiltonianToTSP input =
            encodeTSPData (hamiltonianTSPData G) by
          simp [rawHamiltonianToTSP, hdecode, hvalid]]
        rw [encodeTSPData_mem_iff, hamiltonianTSPData_hasTour_iff]
        exact hsource
      · have hsource : input ∉ GeneralHAMCYCLE := by
          rintro ⟨decoded, hdecoded, hwellFormed, htarget, _⟩
          have hG : G = decoded := Option.some.inj
            (hdecode.symm.trans hdecoded)
          apply hvalid
          simpa [hG] using And.intro hwellFormed htarget
        rw [show rawHamiltonianToTSP input = [] by
          simp [rawHamiltonianToTSP, hdecode, hvalid]]
        exact iff_of_false hsource hempty

end CLRS.Chapter34.TSPReduction
