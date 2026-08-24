import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle

/-!
# Section 34.5 — NP-complete problems

The represented part of this section proves the typed textbook
CLIQUE-to-VERTEX-COVER complement equivalence and lifts it through the shared
encoding to exact total raw-string semantic reductions in both directions.
Both maps have explicit cubic output-length bounds.  VERTEX-COVER also
has exact finite-certificate semantics and a quadratic certificate-length
bound.  A fixed linear-time TM2 now preserves valid graph syntax and maps
parser failures to a deliberately ill-formed sentinel.  The target/order/
endpoint passes are also composed as a fixed polynomial-time well-formedness
guard, and a verified formatter joins both stages from the original raw input.
Complement-edge generation, the complete reduction and verifier machines,
and VERTEX-COVER NP-completeness remain open at the raw-machine layer.  At the
typed textbook layer, the total VERTEX-COVER-to-HAM-CYCLE construction is now
proved correct in both directions, including the selector-budget argument in
the soundness proof.  The HAM-CYCLE-to-TSP and 3-CNF-SAT-to-SUBSET-SUM chains
remain open.
-/
