import CLRSLean.FourthEdition.Chapter_16
open CLRS.Chapter17.StackExecution
#check execute_conservation
#check execute_pops_le_pushes
#check execute_work_le

#check remove_refines_multiPop
#check execute_outputs_length
#check execute_empty_work_le

def mixed : List (Command Nat) :=
  [.pop, .push 7, .push 8, .multiPop 1, .push 9, .multiPop 100, .pop]
example : (execute [] mixed).stack = [] := by decide
example : (execute [] mixed).outputs = [[], [], [], [8], [], [9, 7], []] := by decide
example : (execute [] mixed).pushes = 3 := by decide
example : (execute [] mixed).pops = 3 := by decide
example : (execute [] mixed).work = 13 := by decide
example : (execute [1, 2, 3] ([.multiPop 2, .push 4, .pop] : List (Command Nat))).stack = [3] := by decide
example : (execute [] ([.multiPop 1000000000] : List (Command Nat))).work = 1 := by decide
example : (execute [1, 2] ([.multiPop 0] : List (Command Nat))).stack = [1, 2] := by decide
