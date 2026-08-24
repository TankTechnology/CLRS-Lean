import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding

/-! # Honest serialized decision-TSP language -/

namespace CLRS.Chapter34

/-- A word belongs to decision-TSP exactly when it canonically decodes to a
well-formed row-major weight matrix admitting a tour within its budget. -/
def GeneralTSP : Language TSPSym :=
  { input | ∃ data, decodeTSPData input = some data ∧ data.HasTour }

theorem mem_generalTSP_iff (input : List TSPSym) :
    input ∈ GeneralTSP ↔
      ∃ data, decodeTSPData input = some data ∧ data.HasTour := by
  rfl

theorem encodeTSPData_mem_iff (data : TSPData) :
    encodeTSPData data ∈ GeneralTSP ↔ data.HasTour := by
  constructor
  · rintro ⟨decoded, hdecode, htour⟩
    have hdecoded : decoded = data := by
      have : some decoded = some data := hdecode.symm.trans
        (decode_encodeTSPData data)
      exact Option.some.inj this
    simpa [hdecoded] using htour
  · intro htour
    exact ⟨data, decode_encodeTSPData data, htour⟩

/-- Textbook name for the honest serialized decision problem. -/
abbrev TSP : Language TSPSym := GeneralTSP

end CLRS.Chapter34
