import CLRSLean.FourthEdition.Chapter_32
import CLRSLean.Audit.Axioms
open CLRS.Chapter32

-- One cached table and one transition request per text character, including empty patterns.
example : (DFAExecution.execute [0,1] [0,1] [0,1,0,1]).positions = [0,2] := by decide
example : (DFAExecution.execute [0,1] [0,1] [0,1,0,1]).cells = 6 := by decide
example : (DFAExecution.execute [0,1] [] [0,1]).positions = [0,1,2] := by decide
example : (DFAExecution.execute [0,1] [] [0,1]).transitions = 2 := by decide
example : (DFAExecution.execute [0,1] [0,1,0] [0]).positions = [] := by decide

-- All hashes collide modulo one; literal confirmation still returns exactly the matches.
example : (RKExecution.execute [0,1,0,1] [0,1] 10 1 id).positions = [0,2] := by decide
example : (RKExecution.execute [0,1,0,1] [0,1] 10 1 id).powerMultiplications = 2 := by decide
example : (RKExecution.execute [0,1,0,1] [0,1] 10 1 id).hashCharacters = 4 := by decide
example : (RKExecution.execute [0,1,0,1] [0,1] 10 1 id).slides = 2 := by decide
example : RKExecution.chargedWork (RKExecution.execute [0,1,0,1] [0,1] 10 1 id) = 37 := by decide
example : (RKExecution.execute [1,2] [] 10 7 id).positions = [0,1,2] := by decide
example : (RKExecution.execute [1] [1,2] 10 7 id).positions = [] := by decide
example : hash 10 0 id ([1,2] : List Nat) = 12 := by decide

#assert_axioms RKExecution.execute_correct
#assert_axioms RKExecution.execute_chargedWork
#assert_axioms DFAExecution.execute_correct
#assert_axioms DFAExecution.execute_transitions
#assert_axioms DFAExecution.execute_cells
