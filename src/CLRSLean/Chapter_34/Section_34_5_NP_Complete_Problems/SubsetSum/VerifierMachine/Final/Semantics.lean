import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine.Final.Basic
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.MaskCertificate.Semantics

/-! # Exact arbitrary-input semantics of the concrete SUBSET-SUM verifier -/

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.Final

theorem concreteSubsetSumVerifier_encode_iff (mask : List Bool)
    (data : SubsetSumData) :
    concreteSubsetSumVerifier
        (encodeSubsetSumMask mask, encodeSubsetSumData data) = true ↔
      data.MaskSumsTo mask := by
  simp [concreteSubsetSumVerifier, Syntax.instanceSyntax_encode,
    Syntax.maskSyntax_encode, SumCheck.sumCheck_encode_iff]

theorem concreteSubsetSumVerifier_eq_true_iff
    (certificate input : List SubsetSumSym) :
    concreteSubsetSumVerifier (certificate, input) = true ↔
      ∃ data mask,
        decodeSubsetSumData input = some data ∧
        certificate = encodeSubsetSumMask mask ∧
        data.MaskSumsTo mask := by
  constructor
  · intro haccept
    have hparts := Bool.and_eq_true_iff.mp haccept
    have hrest := Bool.and_eq_true_iff.mp hparts.2
    rcases (Syntax.instanceSyntax_eq_true_iff_exists_decode input).1
        hparts.1 with ⟨data, hdecode⟩
    rcases (Syntax.maskSyntax_eq_true_iff_exists_encode certificate).1
        hrest.1 with ⟨mask, hcertificate⟩
    have hcanonical := encodeSubsetSumData_eq_of_decode_eq_some
      input data hdecode
    have hencoded : concreteSubsetSumVerifier
        (encodeSubsetSumMask mask, encodeSubsetSumData data) = true := by
      rw [← hcertificate, hcanonical]
      exact haccept
    exact ⟨data, mask, hdecode, hcertificate,
      (concreteSubsetSumVerifier_encode_iff mask data).1 hencoded⟩
  · rintro ⟨data, mask, hdecode, rfl, hsum⟩
    have hcanonical := encodeSubsetSumData_eq_of_decode_eq_some
      input data hdecode
    rw [← hcanonical]
    exact (concreteSubsetSumVerifier_encode_iff mask data).2 hsum

theorem mem_generalSUBSETSUM_iff_exists_concrete_certificate
    (input : List SubsetSumSym) :
    input ∈ GeneralSUBSETSUM ↔
      ∃ certificate,
        concreteSubsetSumVerifier (certificate, input) = true := by
  constructor
  · rintro ⟨data, hdecode, hhas⟩
    rcases (hasSubsetSum_iff_exists_mask data).1 hhas with ⟨mask, hsum⟩
    exact ⟨encodeSubsetSumMask mask,
      (concreteSubsetSumVerifier_eq_true_iff _ _).2
        ⟨data, mask, hdecode, rfl, hsum⟩⟩
  · rintro ⟨certificate, haccept⟩
    rcases (concreteSubsetSumVerifier_eq_true_iff _ _).1 haccept with
      ⟨data, mask, hdecode, _, hsum⟩
    exact ⟨data, hdecode, (hasSubsetSum_iff_exists_mask data).2 ⟨mask, hsum⟩⟩

end CLRS.Chapter34.Turing.SubsetSumVerifier.Final
