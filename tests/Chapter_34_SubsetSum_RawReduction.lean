import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum

open CLRS.Chapter34
open CLRS.Chapter34.SubsetSumReduction

#check cnfToSubsetSumData_correct
#check encodeCnfToSubsetSum_mem_iff
#check rawThreeCNFToSubsetSum_correct
#check cnfVarCount_decodeCNF_le
#check rawThreeCNFToSubsetSum_length_le

example (input : List CNFSym) :
    input ∈ ThreeCNFSat ↔
      rawThreeCNFToSubsetSum input ∈ GeneralSUBSETSUM :=
  rawThreeCNFToSubsetSum_correct input

#print axioms CLRS.Chapter34.SubsetSumReduction.cnfToSubsetSumData_correct
#print axioms CLRS.Chapter34.SubsetSumReduction.rawThreeCNFToSubsetSum_correct
#print axioms CLRS.Chapter34.SubsetSumReduction.rawThreeCNFToSubsetSum_length_le
