import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.CertificateColumns

/-!
# Completeness of the 3-CNF-SAT to SUBSET-SUM reduction
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- A satisfying assignment selects one variable item and enough slack items
in every clause to reach the packed target. -/
theorem cnfToSubsetSum_complete {formula : CNF}
    (hthree : IsThreeCNF formula) :
    CnfSatisfiable formula → (cnfToSubsetSum formula).HasSubsetSum := by
  rintro ⟨assignment, heval⟩
  refine ⟨assignmentItems formula assignment,
    assignmentItems_subset formula assignment, ?_⟩
  exact sum_assignmentItems_eq_target hthree heval

end CLRS.Chapter34.SubsetSumReduction
