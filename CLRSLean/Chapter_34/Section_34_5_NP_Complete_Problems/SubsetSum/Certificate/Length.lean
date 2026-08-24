import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Certificate.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Canonicality
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.Length
import Mathlib.Tactic

/-! # Quadratic SUBSET-SUM certificate length -/

namespace CLRS.Chapter34

theorem subsetSum_valueCount_le_input_length
    {input : List SubsetSumSym} {data : SubsetSumData}
    (hdecode : decodeSubsetSumData input = some data) :
    data.values.length ≤ input.length := by
  have hcanonical := encodeSubsetSumData_eq_of_decode_eq_some input data hdecode
  have hcount := encodeTSPFields_count_le_length (data.target :: data.values)
  rw [← hcanonical, encodeSubsetSumData_length]
  simp only [List.length_cons] at hcount
  omega

theorem exists_bounded_subsetSumCertificate_of_mem
    {input : List SubsetSumSym} (hmem : input ∈ GeneralSUBSETSUM) :
    ∃ certificate,
      certificate.length ≤ (input.length + 2) ^ 2 ∧
      subsetSumVerifier certificate input = true := by
  rcases hmem with
    ⟨data, hdecode, indices, hnodup, hrange, hsum⟩
  refine ⟨encodeSubsetSumCertificate indices, ?_, ?_⟩
  · have hfields := encodeTSPFields_length_le_of_lt hrange
    have hcard : indices.length ≤ data.values.length := by
      have hfinsetCard : indices.toFinset.card = indices.length := by
        simpa using List.toFinset_card_of_nodup hnodup
      have hsubset : indices.toFinset ⊆ Finset.range data.values.length := by
        intro index hindex
        rw [List.mem_toFinset] at hindex
        exact Finset.mem_range.mpr (hrange index hindex)
      rw [← hfinsetCard]
      simpa using Finset.card_le_card hsubset
    have hinput := subsetSum_valueCount_le_input_length hdecode
    rw [encodeSubsetSumCertificate_length]
    nlinarith
  · exact (subsetSumVerifier_eq_true_iff _ _).2
      ⟨data, indices, hdecode, decode_encodeSubsetSumCertificate indices,
        hnodup, hrange, hsum⟩

theorem mem_generalSUBSETSUM_iff_exists_bounded_certificate
    (input : List SubsetSumSym) :
    input ∈ GeneralSUBSETSUM ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 2) ^ 2 ∧
        subsetSumVerifier certificate input = true := by
  constructor
  · exact exists_bounded_subsetSumCertificate_of_mem
  · rintro ⟨certificate, _, hverify⟩
    exact (mem_generalSUBSETSUM_iff_exists_certificate input).2
      ⟨certificate, hverify⟩

end CLRS.Chapter34
