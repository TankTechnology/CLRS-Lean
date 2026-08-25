import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Certificate.Length
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.VerifierMachine
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-! # General SUBSET-SUM is in NP -/

namespace CLRS.Chapter34

private theorem exists_bounded_mask_certificate_of_mem
    {input : List SubsetSumSym} (hmem : input ∈ GeneralSUBSETSUM) :
    ∃ certificate,
      certificate.length ≤ input.length + 2 ∧
      Turing.SubsetSumVerifier.Final.concreteSubsetSumVerifier
        (certificate, input) = true := by
  rcases hmem with ⟨data, hdecode, hhas⟩
  rcases (hasSubsetSum_iff_exists_finset data).1 hhas with ⟨chosen, hsum⟩
  let mask := subsetMaskOfFinset chosen
  have hmask : data.MaskSumsTo mask := by
    rw [SubsetSumData.MaskSumsTo, subsetSumMaskOfFinset_sum]
    exact hsum
  refine ⟨encodeSubsetSumMask mask, ?_, ?_⟩
  · rw [encodeSubsetSumMask_length]
    have hmaskLength : mask.length = data.values.length := by
      simp [mask, subsetMaskOfFinset]
    rw [hmaskLength]
    exact Nat.add_le_add_right (subsetSum_valueCount_le_input_length hdecode) 2
  · exact
      (Turing.SubsetSumVerifier.Final.concreteSubsetSumVerifier_eq_true_iff
        _ _).2 ⟨data, mask, hdecode, rfl, hmask⟩

theorem mem_generalSUBSETSUM_iff_exists_bounded_mask_certificate
    (input : List SubsetSumSym) :
    input ∈ GeneralSUBSETSUM ↔
      ∃ certificate,
        certificate.length ≤ input.length + 2 ∧
        Turing.SubsetSumVerifier.Final.concreteSubsetSumVerifier
          (certificate, input) = true := by
  constructor
  · exact exists_bounded_mask_certificate_of_mem
  · rintro ⟨certificate, _, haccept⟩
    exact
      (Turing.SubsetSumVerifier.Final.mem_generalSUBSETSUM_iff_exists_concrete_certificate
        input).2
        ⟨certificate, haccept⟩

theorem generalSUBSETSUM_polyTimeVerifiable :
    PolyTimeVerifiable GeneralSUBSETSUM := by
  refine ⟨fun certificate input =>
      Turing.SubsetSumVerifier.Final.concreteSubsetSumVerifier
        (certificate, input),
    Polynomial.X + 2, ?_, ?_⟩
  · exact ⟨Turing.SubsetSumVerifier.Final.computableInPolyTime⟩
  · intro input
    simpa [Polynomial.eval_add, Polynomial.eval_X] using
      mem_generalSUBSETSUM_iff_exists_bounded_mask_certificate input

theorem SUBSETSUM_mem_ClassNP : SUBSETSUM ∈ ClassNP SubsetSumSym :=
  (mem_ClassNP SUBSETSUM).2 generalSUBSETSUM_polyTimeVerifiable

end CLRS.Chapter34
