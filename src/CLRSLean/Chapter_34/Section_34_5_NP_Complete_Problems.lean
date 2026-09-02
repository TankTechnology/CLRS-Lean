import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum

/-!
# Section 34.5 — NP-complete problems

This section closes the selected textbook chain at both its mathematical and
serialized complexity-theory layers.  CLIQUE and VERTEX-COVER are connected
by exact total raw-string reductions in both directions, explicit output-size
bounds, bounded certificates, fixed polynomial-time reduction and verifier
machines, and {lit}`VERTEXCOVER_npComplete`.

The total CLRS VERTEX-COVER-to-HAM-CYCLE gadget is correct in both directions,
including selector-budget soundness.  HAM-CYCLE has an honest raw language,
bounded certificate semantics, a fixed verifier, and a guarded fixed
polynomial-time reduction, yielding {lit}`HAMCYCLE_npComplete`.  The exact
HAM-CYCLE-to-decision-TSP tour-cost bridge is likewise lifted to an honest raw
language, certificate checker, fixed reduction and verifier machines, and
{lit}`TSP_npComplete`.  Finally, the indexed natural-number
3-CNF-SAT-to-SUBSET-SUM construction has explicit carry-free packing,
assignment and inverse-assignment semantics, a total guarded bit-level
generator with polynomial runtime, a fixed verifier, and
{lit}`SUBSETSUM_npComplete`.
-/
