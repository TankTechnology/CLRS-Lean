import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Completeness
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Soundness

/-!
# Correctness of the 3-CNF-SAT to SUBSET-SUM reduction
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- The concrete carry-free natural-number construction has a subset summing
to its target exactly when the source 3-CNF formula is satisfiable. -/
theorem cnfToSubsetSum_correct {formula : CNF}
    (hthree : IsThreeCNF formula) :
    CnfSatisfiable formula ↔ (cnfToSubsetSum formula).HasSubsetSum :=
  ⟨cnfToSubsetSum_complete hthree, cnfToSubsetSum_sound hthree⟩

end CLRS.Chapter34.SubsetSumReduction
