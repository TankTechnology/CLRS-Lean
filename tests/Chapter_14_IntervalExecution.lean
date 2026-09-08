import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_14.Section_14_2_Matrix_Chain_Multiplication.Execution
import CLRSLean.FourthEdition.Chapter_14.Section_14_5_Optimal_Binary_Search_Trees.Execution

open CLRS.Chapter15

#check MatrixChainExecution.execute_get_correct
#check MatrixChainExecution.execute_candidateVisits
#check MatrixChainExecution.executePlan_correct
#check OBST.Execution.execute_get_correct
#check OBST.Execution.execute_candidateVisits
#check OBST.Execution.executePlan_correct

#assert_axioms DPExecution.buildLayers_evaluatedStates_nodup
#assert_axioms MatrixChainExecution.execute_get_correct
#assert_axioms MatrixChainExecution.executePlan_correct
#assert_axioms OBST.Execution.execute_get_correct
#assert_axioms OBST.Execution.executePlan_correct

private def dims : Nat → Nat := fun i => ([30,35,15,5,10,20,25][i]?).getD 1

-- Six matrices, stored optimum 15125; no recursive oracle is called by execute.
example : (DPExecution.get (MatrixChainExecution.execute dims 5).rows 5 0).cost = 15125 := by
  decide
example : (MatrixChainExecution.execute dims 5).cellWrites = 21 ∧
    (MatrixChainExecution.execute dims 5).candidateVisits = 35 := by decide
example : (MatrixChainExecution.execute dims 5).evaluatedStates.count (3,1) = 1 := by decide

-- Reconstruction reads the same stored split table and attains the optimum.
example : ChainPlan.cost dims (MatrixChainExecution.executePlan dims 5).1 = 15125 := by
  rw [MatrixChainExecution.executePlan_cost]; decide
example (d : Nat → Nat) (N : Nat) (other : ChainPlan 0 N) :
    ChainPlan.cost d (MatrixChainExecution.executePlan d N).1 ≤ ChainPlan.cost d other :=
  MatrixChainExecution.executePlan_correct d N other

-- Zero maximum index means one matrix, with a zero cost and no candidates.
example : (DPExecution.get (MatrixChainExecution.execute dims 0).rows 0 0).cost = 0 ∧
    (MatrixChainExecution.execute dims 0).cellWrites = 1 ∧
    (MatrixChainExecution.execute dims 0).candidateVisits = 0 := by decide

-- Tied costs retain the earliest scanned split.
example : (DPExecution.get (MatrixChainExecution.execute (fun _ => 0) 3).rows 3 0).split = 0 := by
  decide

private def p : Nat → Nat := fun i => ([0,15,10,5,10,20][i]?).getD 0
private def q : Nat → Nat := fun i => ([5,10,5,5,5,10][i]?).getD 0

-- Natural weights scaled by 100: the independent example has optimum 275.
example : (DPExecution.get (OBST.Execution.execute p q 5).rows 5 0).cost = 275 := by decide
example : (DPExecution.get (OBST.Execution.execute p q 5).rows 5 0).weight = 100 := by decide
example : (OBST.Execution.execute p q 5).cellWrites = 21 ∧
    (OBST.Execution.execute p q 5).candidateVisits = 35 := by decide
example : OBST.expectedCost p q (OBST.Execution.executePlan p q 5).1 = 275 := by
  rw [OBST.Execution.executePlan_cost]; decide

-- Empty key interval retains its dummy weight, unlike a one-matrix interval.
example : (DPExecution.get (OBST.Execution.execute p q 0).rows 0 0).cost = 5 ∧
    (OBST.Execution.execute p q 0).candidateVisits = 0 := by decide

-- All-zero weights remain valid and select the first admissible root.
example : (DPExecution.get (OBST.Execution.execute (fun _ => 0) (fun _ => 0) 3).rows 3 0).root = 1 := by
  decide

example (p q : Nat → Nat) (N : Nat) (other : OBST.BSTPlan 0 N) :
    OBST.expectedCost p q (OBST.Execution.executePlan p q N).1 ≤ OBST.expectedCost p q other :=
  OBST.Execution.executePlan_correct p q N other

-- Once-per-state is obtained by concrete instantiation of the shared runner.
example (d : Nat → Nat) (N : Nat) : (MatrixChainExecution.execute d N).evaluatedStates.Nodup :=
  MatrixChainExecution.execute_once d N
example (p q : Nat → Nat) (N : Nat) : (OBST.Execution.execute p q N).evaluatedStates.Nodup :=
  OBST.Execution.execute_once p q N
example (d : Nat → Nat) (N l i : Nat) :
    (l,i) ∈ (MatrixChainExecution.execute d N).evaluatedStates ↔ i+l ≤ N :=
  MatrixChainExecution.execute_state_iff d N l i
