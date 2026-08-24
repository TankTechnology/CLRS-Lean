import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Runtime

/-!
# Graph syntax-normalizer machine

This facade exports the fixed linear-time TM2 that preserves canonical graph
syntax and maps parser failures to a canonical but deliberately ill-formed
sentinel.  The later complement controller can therefore handle parse failure
and graph-invariant failure through one shared rejection branch.
-/
