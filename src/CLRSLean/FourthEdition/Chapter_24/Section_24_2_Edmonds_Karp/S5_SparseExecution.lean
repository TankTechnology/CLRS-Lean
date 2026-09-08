import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.SparseExecution.Execution

/-!
# Sparse counted Edmonds–Karp execution

The sparse input enumerates all positive capacity arcs without repetition.
Preparation inserts each arc and its reverse once. Every iteration uses one
support BFS, reconstructs its saved parent chain, scans that path's bottleneck,
and updates its forward/reverse flow entries. The resulting flow is maximal.

The actual timeline yields at most 2VE augmentations and at most 130VE² work
when E>0, including preparation and failed searches; E=0 costs at most V+2.
Here V counts all vertices, including isolated vertices, and E counts positive
capacity arcs. These are unit-cost dictionary, bucket, queue and exact-real
operations, following the existing support-BFS model; persistent-container
copying and bit complexity are outside this model. No equality with the older
classical-choice Edmonds–Karp path sequence is asserted.
-/
