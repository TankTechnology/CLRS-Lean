import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum

/-!
# Section 34.5 — NP-complete problems

The represented part of this section proves the typed textbook
CLIQUE-to-VERTEX-COVER complement equivalence and lifts it through the shared
encoding to exact total raw-string semantic reductions in both directions.
Both maps have explicit cubic output-length bounds.  VERTEX-COVER also
has exact finite-certificate semantics and a quadratic certificate-length
bound.  Its normalization, graph guard, complement emitter, total reduction,
and complement-clique verifier are implemented by fixed polynomial-time TM2
machines on the complete raw encoding.  Consequently
`generalCLIQUE_reducible_to_VERTEXCOVER`,
`VERTEXCOVER_mem_ClassNP`, and `VERTEXCOVER_npComplete` close the
strict serialized VERTEX-COVER layer.  At the typed textbook layer, the total
VERTEX-COVER-to-HAM-CYCLE construction is now
proved correct in both directions, including the selector-budget argument in
the soundness proof.  The typed HAM-CYCLE-to-decision-TSP construction is also
proved correct in both directions using the exact tour-cost identity.  The
typed 3-CNF-SAT-to-SUBSET-SUM construction is proved correct in both
directions as well: its indexed natural-number items, carry-free packing,
assignment certificate, and inverse assignment extraction are all explicit.
HAM-CYCLE still needs its raw reduction and verifier machines plus NP wrappers;
TSP and SUBSET-SUM additionally need honest raw languages and certificate
interfaces before their fixed-machine and NP-completeness layers can close.
-/
