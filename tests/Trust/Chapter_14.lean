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

#check CLRS.Chapter15.LCSTabulation.execute_row
#assert_axioms CLRS.Chapter15.LCSTabulation.execute_row
#check CLRS.Chapter15.LCSTabulation.execute_row_length
#assert_axioms CLRS.Chapter15.LCSTabulation.execute_row_length
#check CLRS.Chapter15.lcsLengthTabulated_correct
#assert_axioms CLRS.Chapter15.lcsLengthTabulated_correct
#check CLRS.Chapter15.lcsLengthTabulated_upper_bound
#assert_axioms CLRS.Chapter15.lcsLengthTabulated_upper_bound
#check CLRS.Chapter15.lcsExecution_cells_bounds
#assert_axioms CLRS.Chapter15.lcsExecution_cells_bounds
#check CLRS.Chapter15.RodExecution.execute_entry
#assert_axioms CLRS.Chapter15.RodExecution.execute_entry
#check CLRS.Chapter15.RodExecution.execute_writes
#assert_axioms CLRS.Chapter15.RodExecution.execute_writes
#check CLRS.Chapter15.rodExecution_candidates_eq
#assert_axioms CLRS.Chapter15.rodExecution_candidates_eq
#check CLRS.Chapter15.rodExecution_candidates_le_quadratic
#assert_axioms CLRS.Chapter15.rodExecution_candidates_le_quadratic
#check CLRS.Chapter15.DPExecution.buildLayers_property
#assert_axioms CLRS.Chapter15.DPExecution.buildLayers_property
#check CLRS.Chapter15.DPExecution.buildLayers_cellWrites
#assert_axioms CLRS.Chapter15.DPExecution.buildLayers_cellWrites
#check CLRS.Chapter15.DPExecution.buildLayers_candidateVisits
#assert_axioms CLRS.Chapter15.DPExecution.buildLayers_candidateVisits
#check CLRS.Chapter15.MatrixChainExecution.execute_get_correct
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_get_correct
#check CLRS.Chapter15.MatrixChainExecution.executePlan_correct
#assert_axioms CLRS.Chapter15.MatrixChainExecution.executePlan_correct
#check CLRS.Chapter15.MatrixChainExecution.execute_cells
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_cells
#check CLRS.Chapter15.MatrixChainExecution.execute_candidateVisits
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_candidateVisits
#check CLRS.Chapter15.OBST.Execution.execute_get_correct
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_get_correct
#check CLRS.Chapter15.OBST.Execution.executePlan_correct
#assert_axioms CLRS.Chapter15.OBST.Execution.executePlan_correct
#check CLRS.Chapter15.OBST.Execution.execute_cells
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_cells
#check CLRS.Chapter15.OBST.Execution.execute_candidateVisits
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_candidateVisits

#check CLRS.Chapter15.MatrixChainExecution.execute_once
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_once
#check CLRS.Chapter15.MatrixChainExecution.execute_state_iff
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_state_iff
#check CLRS.Chapter15.MatrixChainExecution.execute_cells_closed
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_cells_closed
#check CLRS.Chapter15.MatrixChainExecution.execute_candidateVisits_closed
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_candidateVisits_closed
#check CLRS.Chapter15.MatrixChainExecution.execute_cells_bounds
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_cells_bounds
#check CLRS.Chapter15.MatrixChainExecution.execute_candidateVisits_bounds
#assert_axioms CLRS.Chapter15.MatrixChainExecution.execute_candidateVisits_bounds
#check CLRS.Chapter15.MatrixChainExecution.executePlan_cost
#assert_axioms CLRS.Chapter15.MatrixChainExecution.executePlan_cost
#check CLRS.Chapter15.OBST.Execution.execute_once
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_once
#check CLRS.Chapter15.OBST.Execution.execute_state_iff
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_state_iff
#check CLRS.Chapter15.OBST.Execution.execute_cells_closed
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_cells_closed
#check CLRS.Chapter15.OBST.Execution.execute_candidateVisits_closed
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_candidateVisits_closed
#check CLRS.Chapter15.OBST.Execution.execute_cells_bounds
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_cells_bounds
#check CLRS.Chapter15.OBST.Execution.execute_candidateVisits_bounds
#assert_axioms CLRS.Chapter15.OBST.Execution.execute_candidateVisits_bounds
#check CLRS.Chapter15.OBST.Execution.executePlan_cost
#assert_axioms CLRS.Chapter15.OBST.Execution.executePlan_cost
