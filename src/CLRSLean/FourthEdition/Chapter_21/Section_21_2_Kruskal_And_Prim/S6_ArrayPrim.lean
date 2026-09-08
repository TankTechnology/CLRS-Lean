import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.ArrayPrim.Correctness

/-!
# Prim with a cached array queue

This companion provides an executable incremental Prim algorithm over stored
adjacency lists. It constructs a minimum spanning tree under the chapter's
graph assumptions. Its own generated array-cell work is at most
2n² + 5n + 6|E|, including queue and index-list preparation. No binary-heap
operation trace or caller-supplied update counts occur in this interface.
The bound counts cell operations and key comparisons, not persistent-array
copying or integer bit operations. The ambient index bound n equals |V| when
the graph's vertex set is the full finite index universe.
-/
