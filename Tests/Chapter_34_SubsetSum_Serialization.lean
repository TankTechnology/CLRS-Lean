import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum

open CLRS.Chapter34

#check GeneralSUBSETSUM
#check SUBSETSUM
#check subsetSumVerifier_eq_true_iff
#check mem_generalSUBSETSUM_iff_exists_bounded_certificate

private def sampleSubsetSumData : SubsetSumData where
  target := 9
  values := [4, 9, 5, 9]

example : encodeSubsetSumData sampleSubsetSumData ∈ GeneralSUBSETSUM := by
  rw [encodeSubsetSumData_mem_iff]
  refine ⟨[0, 2], by decide, ?_, by decide⟩
  intro index hindex
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hindex
  rcases hindex with rfl | rfl
  · decide
  · decide

example :
    subsetSumVerifier
        (encodeSubsetSumCertificate [1])
        (encodeSubsetSumData sampleSubsetSumData) = true := by
  rw [subsetSumVerifier_eq_true_iff]
  exact ⟨sampleSubsetSumData, [1], decode_encodeSubsetSumData _,
    decode_encodeSubsetSumCertificate _, by decide, by decide, by decide⟩

#print axioms CLRS.Chapter34.subsetSumVerifier_eq_true_iff
#print axioms CLRS.Chapter34.mem_generalSUBSETSUM_iff_exists_bounded_certificate
