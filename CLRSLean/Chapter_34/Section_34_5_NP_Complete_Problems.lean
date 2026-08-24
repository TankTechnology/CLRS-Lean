import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover

/-!
# Section 34.5 — NP-complete problems

The represented part of this section proves the typed textbook
CLIQUE-to-VERTEX-COVER complement equivalence and lifts it through the shared
encoding to exact total raw-string semantic reductions in both directions.
Both maps have explicit cubic output-length bounds.  VERTEX-COVER also
has exact finite-certificate semantics and a quadratic certificate-length
bound.  A fixed linear-time TM2 now preserves valid graph syntax and maps
parser failures to a deliberately ill-formed sentinel.  The remaining
complement and verifier machines, VERTEX-COVER NP-completeness, and the
HAM-CYCLE, TSP, and SUBSET-SUM chains remain open.
-/
