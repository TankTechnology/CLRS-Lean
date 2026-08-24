import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.RawReduction

/-!
# VERTEX-COVER

This facade exports the first formalized layers of CLRS Section 34.5: the
shared graph-plus-target representation, deterministic graph complement, the
textbook equivalence between a size-`k` clique and a size-at-most `|V| - k`
cover in the complemented graph, and its exact lift to a total raw-string map.

The fixed polynomial-time complement machine, VERTEX-COVER verifier and NP
membership, and NP-completeness theorem are not claimed by this facade yet.
-/
