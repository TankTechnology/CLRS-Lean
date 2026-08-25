import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_35

/-! # Chapter 35 flagship trust surface -/

#check CLRS.ApproxVertexCover.Graph.approxVertexCover_two_approx
#check CLRS.TSP.TreeOn.tsp_two_approx
#check CLRS.ApproxSubsetSum.approxSubsetSum_fptas

#assert_axioms CLRS.ApproxVertexCover.Graph.approxVertexCover_two_approx
#assert_axioms CLRS.TSP.TreeOn.tsp_two_approx
#assert_axioms CLRS.ApproxSubsetSum.approxSubsetSum_fptas
