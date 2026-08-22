# Chapter 34 basic textbook closure — 2026-08-22

## Outcome

The main Cook--Levin theorem was already closed before this checkpoint:
`cookLevinMap_polyTimeComputable` supplies the fixed polynomial-time map
compiler, `cookLevin_theorem` supplies the universal reduction, and
`generalCircuitSAT_npComplete` proves the honest serialized general-circuit
language NP-complete.

This checkpoint closes the remaining direct textbook bridge from that honest
general-circuit language to SAT at the semantic and representation-size level.

| Boundary | Public theorem | Status |
| --- | --- | --- |
| Circuit consistency formula | `generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula` | proved |
| Total raw-string map | `generalCircuitToSATMap` | defined |
| Exact raw-language semantics | `generalCircuitToSATMap_mem_SAT_iff` | proved |
| Polynomial output size | `generalCircuitToSATMap_length_le` | proved, `32 * (n + 1)^3` |

Malformed circuit encodings and decoded but ill-formed circuits map to the
canonical false formula.  Consequently the language theorem quantifies over
all raw input strings, not only a hidden well-formed subset.

## Acceptance evidence

- `lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT`
- `lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT.lean`
- the interface test's `#print axioms` output contains only the standard
  Mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`
- no project-local axiom or proof hole is introduced by the new bridge

The final branch acceptance also runs the Chapter 34 root build, the Cook--
Levin main-theorem interface, repository policy checks, and the full library
build; their exact results belong in the merge handoff rather than being
predicted here.

## Deliberately deferred boundary

This basic closure does not claim more than was proved.  The following remain
separate work:

- a concrete polynomial-time TM2 for the new direct
  `generalCircuitToSATMap`;
- a concrete NP verifier and `SAT ∈ NP` theorem for the current SAT encoding;
- an honest general graph-plus-`k` CLIQUE language and checker;
- the Section 34.5 decision-problem reduction chain, including VERTEX-COVER,
  HAM-CYCLE, TSP, and SUBSET-SUM.

The first two are refinement work.  The latter two are the principal remaining
textbook-coverage gaps, so Chapter 34 correctly remains `partial`.
