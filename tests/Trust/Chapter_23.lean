import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_23

/-! # Chapter 23 flagship trust surface -/

#check CLRS.Chapter24.WeightedGraph.floydWarshall_isShortestDist
#check CLRS.Chapter24.WeightedGraph.johnsonAllPairsDist_correct
#check CLRS.Chapter24.WeightedGraph.johnsonCost_eq

#assert_axioms CLRS.Chapter24.WeightedGraph.floydWarshall_isShortestDist
#assert_axioms CLRS.Chapter24.WeightedGraph.johnsonAllPairsDist_correct
#assert_axioms CLRS.Chapter24.WeightedGraph.johnsonCost_eq

example (G : CLRS.Chapter24.WeightedGraph (Fin 3)) : G.floydWarshallCost = 27 := by
  simpa using CLRS.Chapter24.WeightedGraph.floydWarshall_O_cubed G

#assert_axioms CLRS.Chapter24.WeightedGraph.cycleFloydWarshall_negative_iff
#assert_axioms CLRS.Chapter24.WeightedGraph.detectsNegativeCycle_iff
#assert_axioms CLRS.Chapter24.MatrixExecution.floyd_read
#assert_axioms CLRS.Chapter24.MatrixExecution.square_read
#assert_axioms CLRS.Chapter24.MatrixExecution.diagonalScan_negative_iff
#assert_axioms CLRS.Chapter24.MatrixExecution.fasterOn_visits_eq_budget
#assert_axioms CLRS.Chapter24.MatrixExecution.cycleFloydOn_visits_eq_budget

#assert_axioms CLRS.Chapter24.JohnsonExecution.johnsonStored_read
#assert_axioms CLRS.Chapter24.JohnsonExecution.johnsonStored_correct
#assert_axioms CLRS.Chapter24.JohnsonExecution.johnsonStored_work_le_polynomial
#assert_axioms CLRS.Chapter24.JohnsonExecution.johnsonStored_row
