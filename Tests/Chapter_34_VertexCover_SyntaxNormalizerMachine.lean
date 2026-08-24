import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Runtime

/-!
# Regression test: raw graph syntax-normalizer TM2
-/

open CLRS Chapter34
open CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer

#check malformedGraphSentinel
#check malformedGraphSentinel_not_wellFormed
#check normalizedInstanceValue
#check normalizedStream_eq
#check run
#check steps_le
#check computableInPolyTime

#print axioms normalizedStream_eq
#print axioms run
#print axioms computableInPolyTime
