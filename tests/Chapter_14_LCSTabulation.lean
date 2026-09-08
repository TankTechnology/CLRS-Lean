import CLRSLean.FourthEdition.Chapter_14
open CLRS.Chapter15
#check LCSTabulation.execute_row
#check LCSTabulation.execute_cells
#check lcsLengthTabulated_correct

#check lcsExecution_cells_bounds
#check LCSTabulation.execute_row_length
example : lcsLengthTabulated ([1, 2, 3, 4] : List Nat) [2, 4, 3] = 2 := by decide
example : lcsLengthTabulated (List.replicate 8 (0 : Nat)) (List.replicate 8 1) = 0 := by decide
example : (LCSTabulation.execute (List.replicate 8 (0 : Nat)) (List.replicate 8 1)).cells = 81 := by decide
example : (LCSTabulation.execute ([] : List Nat) [1, 2, 3]).cells = 4 := by decide
example : (LCSTabulation.execute ([1, 2, 3] : List Nat) []).cells = 4 := by decide
example : lcsLengthTabulated ([1, 2, 1] : List Nat) [1, 2, 1] = 3 := by decide
