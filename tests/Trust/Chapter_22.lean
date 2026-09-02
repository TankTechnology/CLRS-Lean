import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_22

/-! # Chapter 22 flagship trust surface -/

#check CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist
#check CLRS.Chapter24.WeightedGraph.bellmanFordWork_le
#check CLRS.Chapter24.WeightedGraph.dijkstraLoop_correct

#assert_axioms CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist
#assert_axioms CLRS.Chapter24.WeightedGraph.bellmanFordWork_le
#assert_axioms CLRS.Chapter24.WeightedGraph.dijkstraLoop_correct

example : CLRS.Chapter24.WeightedGraph.dijkstraWork 4 5 = 27 := by
  decide
