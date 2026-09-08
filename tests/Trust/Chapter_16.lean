import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_16

/-! # Chapter 16 flagship trust surface -/

#check CLRS.Chapter17.multiPop_totalCost_le
#check CLRS.Chapter17.binaryCounter_trace_totalFlips_le
#check CLRS.Chapter17.trace_totalCost_le_three_mul

#assert_axioms CLRS.Chapter17.multiPop_totalCost_le
#assert_axioms CLRS.Chapter17.binaryCounter_trace_totalFlips_le
#assert_axioms CLRS.Chapter17.trace_totalCost_le_three_mul

example : CLRS.Chapter17.multiPop [1, 2, 3] 2 = [3] := by
  decide

#check CLRS.Chapter17.StackExecution.remove_refines_multiPop
#assert_axioms CLRS.Chapter17.StackExecution.remove_refines_multiPop
#check CLRS.Chapter17.StackExecution.remove_removed
#assert_axioms CLRS.Chapter17.StackExecution.remove_removed
#check CLRS.Chapter17.StackExecution.execute_conservation
#assert_axioms CLRS.Chapter17.StackExecution.execute_conservation
#check CLRS.Chapter17.StackExecution.execute_pops_le_pushes
#assert_axioms CLRS.Chapter17.StackExecution.execute_pops_le_pushes
#check CLRS.Chapter17.StackExecution.execute_work_le
#assert_axioms CLRS.Chapter17.StackExecution.execute_work_le
#check CLRS.Chapter17.StackExecution.execute_outputs_length
#assert_axioms CLRS.Chapter17.StackExecution.execute_outputs_length
