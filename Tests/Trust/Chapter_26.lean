import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_26

/-! # Chapter 26 flagship trust surface -/

#check CLRS.Chapter27.CompDAG.greedySchedule_time_le_work_div_add_span
#check CLRS.Chapter27.pMergeSort_correct
#check CLRS.Chapter27.strassenWork_allInput_bigTheta

#assert_axioms CLRS.Chapter27.CompDAG.greedySchedule_time_le_work_div_add_span
#assert_axioms CLRS.Chapter27.pMergeSort_correct
#assert_axioms CLRS.Chapter27.strassenWork_allInput_bigTheta

example : (CLRS.Chapter27.pMergeSort [7]).value = [7] := by
  rw [CLRS.Chapter27.pMergeSort.eq_def]
  norm_num [CLRS.Chapter27.Costed.charge]
