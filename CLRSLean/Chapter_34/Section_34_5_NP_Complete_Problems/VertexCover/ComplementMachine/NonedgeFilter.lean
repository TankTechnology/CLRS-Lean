import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Pipeline

/-!
# VERTEX-COVER complement machine: repeated nonedge filter

The input layer builds the exact candidate-pair/graph stream in polynomial
time.  The remaining operational layer repeatedly scans the restored graph
and emits precisely the failed membership queries.
-/
