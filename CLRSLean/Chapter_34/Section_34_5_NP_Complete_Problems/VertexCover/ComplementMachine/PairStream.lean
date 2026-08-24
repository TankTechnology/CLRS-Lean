import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.Runtime

/-!
# VERTEX-COVER complement machine: canonical vertex-pair stream

The semantic layer identifies the reused general-CLIQUE positional-pair
generator with the exact normalized-pair sequence used by the complement map.
The range-certificate layer supplies its canonical `[0, ..., |V| - 1]` input
directly from the graph encoding with a fixed polynomial-time TM2.  Their
composition computes the exact canonical pair stream from the original graph.
-/
