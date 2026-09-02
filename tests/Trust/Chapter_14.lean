import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_14

/-! # Chapter 14 flagship trust surface -/

#check CLRS.Chapter15.rodCutPlan_optimal
#check CLRS.Chapter15.matrixChainTime_le_cubic
#check CLRS.Chapter15.OBST.obstRoot_optimal

#assert_axioms CLRS.Chapter15.rodCutPlan_optimal
#assert_axioms CLRS.Chapter15.matrixChainTime_le_cubic
#assert_axioms CLRS.Chapter15.OBST.obstRoot_optimal

example : CLRS.Chapter15.rodCutPlan (fun n => n * n) 1 = [1] := by
  norm_num [CLRS.Chapter15.rodCutPlan, CLRS.Chapter15.rodCutFirstCut,
    CLRS.Chapter15.bottomUpRodRevenue, CLRS.Chapter15.rodCutCandidates,
    CLRS.Chapter15.FirstCutValue, CLRS.Chapter15.bestRodCutOf]
