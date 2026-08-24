import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementSemantics

/-!
# VERTEX-COVER

This facade exports the first formalized semantic layer of CLRS Section 34.5:
the shared graph-plus-target representation, deterministic graph complement,
and the textbook equivalence between a size-`k` clique and a size-at-most
`|V| - k` cover in the complemented graph.

The raw VERTEX-COVER language, polynomial-time complement machine, NP
membership, and NP-completeness theorem are not claimed by this facade yet.
-/
