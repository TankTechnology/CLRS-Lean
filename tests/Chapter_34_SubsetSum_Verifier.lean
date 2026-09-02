import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum

open CLRS Chapter34

#check subsetSumVerifier_eq_true_iff
#check hasSubsetSum_iff_exists_mask
#check Turing.SubsetSumVerifier.Final.concreteSubsetSumVerifier_eq_true_iff
#check Turing.SubsetSumVerifier.Final.computableInPolyTime
#check generalSUBSETSUM_polyTimeVerifiable
#check SUBSETSUM_mem_ClassNP

example : SUBSETSUM ∈ ClassNP SubsetSumSym := SUBSETSUM_mem_ClassNP

#print axioms Turing.SubsetSumVerifier.Final.computableInPolyTime
#print axioms generalSUBSETSUM_polyTimeVerifiable
#print axioms SUBSETSUM_mem_ClassNP
