import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.RawWellFormed

/-!
# Regression test: raw graph syntax and well-formedness pipeline
-/

open CLRS Chapter34

open CLRS.Chapter34.Turing.VertexCover.ComplementMachine

#check GraphPairFormatter.format_eq_graphPairEncoding
#check GraphPairFormatter.computableInPolyTime
#check GraphPairFormatter.typedComputableInPolyTime
#check RawWellFormed.rawWellFormedPass
#check RawWellFormed.rawWellFormedPass_eq_true_iff
#check RawWellFormed.computableInPolyTime

#print axioms GraphPairFormatter.computableInPolyTime
#print axioms RawWellFormed.rawWellFormedPass_eq_true_iff
#print axioms RawWellFormed.computableInPolyTime
