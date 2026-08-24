import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.WellFormedGuard
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.RawWellFormed
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream

/-!
# VERTEX-COVER complement-machine components

The raw graph syntax-normalizer is closed at semantic and fixed linear-time
TM2 layers.  The target/order/endpoint conjunction is also closed as a fixed
polynomial-time guard on the established empty-certificate pair encoding.
The graph-pair formatter and composition theorem close the entire original-raw-
input to exact well-formedness-verdict pipeline.  Canonical pair-stream
semantics now reuses the verified general-CLIQUE positional-pair generator.
The graph-header-to-range-certificate bridge, nonedge emission, and final
direction-specific fallback selection remain subsequent components.
-/
