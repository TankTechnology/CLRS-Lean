import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Certificate
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.RawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ReverseRawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMapLength
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine

/-!
# VERTEX-COVER

This facade exports the first formalized layers of CLRS Section 34.5: the
shared graph-plus-target representation, deterministic graph complement, the
textbook equivalence between a size-`k` clique and a size-at-most `|V| - k`
cover in the complemented graph, and its exact lift to total raw-string maps
in both directions.  Both maps factor through one shared guarded complement
function and have explicit cubic output-length bounds.
It also exports an executable Boolean certificate checker, its exact semantics,
and a quadratic accepted-certificate bound.

The raw syntax-normalization phase already has a fixed linear-time TM2, and
the three graph-invariant passes are combined into a fixed polynomial-time
well-formedness guard.  Stream-format composition, complement-edge emission,
the complete reduction/verifier machines, VERTEX-COVER NP membership, and the
NP-completeness theorem are not claimed by this facade yet.
-/
