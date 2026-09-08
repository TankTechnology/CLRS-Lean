import CLRSLean.FourthEdition.Chapter_14
open CLRS.Chapter15
#check RodExecution.execute_array
#check RodExecution.execute_candidates
#check RodExecution.execute_entry

#check rodExecution_candidates_le_quadratic
#check RodExecution.execute_writes
example : (RodExecution.execute (fun n => n * n) 4).array = #[0, 1, 4, 9, 16] := by decide
example : (RodExecution.execute (fun _ => 3) 4).array = #[0, 3, 6, 9, 12] := by decide
example : (RodExecution.execute (fun _ => 0) 4).candidates = 10 := by decide
example : (RodExecution.execute (fun _ => 0) 4).writes = 5 := by decide
example : (RodExecution.execute (fun _ => 100) 0).array = #[0] := by decide
