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
