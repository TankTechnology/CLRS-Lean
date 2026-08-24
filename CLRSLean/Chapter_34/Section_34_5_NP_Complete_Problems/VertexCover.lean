import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Certificate
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.RawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ReverseRawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMapLength
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.VerifierMachine
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.NPCompleteness

/-!
# VERTEX-COVER

This facade exports the first formalized layers of CLRS Section 34.5: the
shared graph-plus-target representation, deterministic graph complement, the
textbook equivalence between a size-`k` clique and a size-at-most `|V| - k`
cover in the complemented graph, and its exact lift to total raw-string maps
in both directions.  Both maps factor through one shared guarded complement
function and have explicit cubic output-length bounds.
It also exports an executable Boolean certificate checker, its exact semantics,
a quadratic accepted-certificate bound, and the textbook NP-completeness
theorem.

The raw syntax-normalization phase, complement emitter, total reduction, and
complement-clique certificate verifier are all realized by fixed polynomial-
time TM2 machines on their complete raw encodings.
-/
