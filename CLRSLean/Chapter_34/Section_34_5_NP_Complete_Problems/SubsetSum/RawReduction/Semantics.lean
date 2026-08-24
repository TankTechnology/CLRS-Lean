import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.Construction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Correctness
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Language

/-! # Correctness of the serialized SUBSET-SUM construction -/

namespace CLRS.Chapter34.SubsetSumReduction

theorem cnfToSubsetSumData_correct {formula : CNF}
    (hthree : IsThreeCNF formula) :
    CnfSatisfiable formula ↔ (cnfToSubsetSumData formula).HasSubsetSum := by
  rw [cnfToSubsetSumData,
    SubsetSumInstance.toDataFromList_hasSubsetSum_iff
    (cnfToSubsetSum formula) (reductionItemList formula)
    (reductionItemList_nodup formula)
    (mem_reductionItemList_iff formula)]
  exact cnfToSubsetSum_correct hthree

theorem encodeCnfToSubsetSum_mem_iff {formula : CNF}
    (hthree : IsThreeCNF formula) :
    encodeCnfToSubsetSum formula ∈ GeneralSUBSETSUM ↔
      CnfSatisfiable formula := by
  rw [encodeCnfToSubsetSum, encodeSubsetSumData_mem_iff]
  exact (cnfToSubsetSumData_correct hthree).symm

theorem subsetSumNoData_not_hasSubsetSum :
    ¬ subsetSumNoData.HasSubsetSum := by
  rintro ⟨indices, _, hrange, _⟩
  cases indices with
  | nil => simp [subsetSumNoData, SubsetSumData.selectedSum] at *
  | cons index rest =>
      have := hrange index (by simp)
      simp [subsetSumNoData] at this

theorem rawThreeCNFToSubsetSum_correct (input : List CNFSym) :
    input ∈ ThreeCNFSat ↔
      rawThreeCNFToSubsetSum input ∈ GeneralSUBSETSUM := by
  by_cases hthree : IsThreeCNF (decodeCNF input)
  · simp only [ThreeCNFSat, Set.mem_setOf_eq, hthree, true_and,
      rawThreeCNFToSubsetSum, if_pos]
    exact (encodeCnfToSubsetSum_mem_iff hthree).symm
  · simp [ThreeCNFSat, rawThreeCNFToSubsetSum, hthree,
      encodeSubsetSumData_mem_iff, subsetSumNoData_not_hasSubsetSum]

end CLRS.Chapter34.SubsetSumReduction
