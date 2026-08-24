import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.WellFormedGuard.Runtime

/-!
# Regression test: fixed graph well-formedness guard
-/

open CLRS Chapter34
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard

#check wellFormedPass
#check wellFormedPass_encode_iff
#check pairComputableInPolyTime
#check graphComputableInPolyTime

#print axioms wellFormedPass_encode_iff
#print axioms pairComputableInPolyTime
#print axioms graphComputableInPolyTime
