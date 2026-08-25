import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.GuardedReduction
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Completeness

/-! # Concrete 3-CNF-SAT to SUBSET-SUM hardness -/

namespace CLRS.Chapter34

/-- The textbook digit construction is a concrete polynomial-time many-one
reduction from serialized three-CNF satisfiability to honest SUBSET-SUM. -/
theorem threeCNFSat_reducible_to_SUBSETSUM :
    PolyTimeReducible ThreeCNFSat SUBSETSUM := by
  refine ⟨SubsetSumReduction.rawThreeCNFToSubsetSum,
    ⟨Turing.SubsetSumReduction.rawThreeCNFToSubsetSum_computableInPolyTime⟩,
    ?_⟩
  intro input
  exact SubsetSumReduction.rawThreeCNFToSubsetSum_correct input

/-- Honest serialized SUBSET-SUM is NP-hard. -/
theorem SUBSETSUM_npHard : NPHard SUBSETSUM :=
  NPHard.of_reducible threeCNFSat_npHard
    threeCNFSat_reducible_to_SUBSETSUM

end CLRS.Chapter34
