import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Certificate.Basic

/-! # Exact SUBSET-SUM certificate semantics -/

namespace CLRS.Chapter34

theorem subsetSumVerifier_eq_true_iff
    (certificate input : List SubsetSumSym) :
    subsetSumVerifier certificate input = true ↔
      ∃ data indices,
        decodeSubsetSumData input = some data ∧
        decodeSubsetSumCertificate certificate = some indices ∧
        indices.Nodup ∧
        (∀ index ∈ indices, index < data.values.length) ∧
        data.selectedSum indices = data.target := by
  generalize hinput : decodeSubsetSumData input = dataResult
  generalize hcertificate : decodeSubsetSumCertificate certificate =
    certificateResult
  cases dataResult <;> cases certificateResult <;>
    simp [subsetSumVerifier, hinput, hcertificate]

theorem mem_generalSUBSETSUM_iff_exists_certificate
    (input : List SubsetSumSym) :
    input ∈ GeneralSUBSETSUM ↔
      ∃ certificate, subsetSumVerifier certificate input = true := by
  constructor
  · rintro ⟨data, hdecode, indices, hnodup, hrange, hsum⟩
    refine ⟨encodeSubsetSumCertificate indices, ?_⟩
    exact (subsetSumVerifier_eq_true_iff _ _).2
      ⟨data, indices, hdecode, decode_encodeSubsetSumCertificate indices,
        hnodup, hrange, hsum⟩
  · rintro ⟨certificate, hverify⟩
    rcases (subsetSumVerifier_eq_true_iff certificate input).1 hverify with
      ⟨data, indices, hdecode, _, hnodup, hrange, hsum⟩
    exact ⟨data, hdecode, indices, hnodup, hrange, hsum⟩

end CLRS.Chapter34
