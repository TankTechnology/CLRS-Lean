# Chapter 34 basic textbook closure — 2026-08-22

> **Historical checkpoint.** Superseded on 2026-08-25: the general CLIQUE and
> selected Section 34.5 chains are now closed, and Chapter 34 is
> `main-proof-complete` at its advertised textbook boundary. The remaining-gap
> discussion below is retained as dated audit evidence.

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

- `lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT.lean`: passed;
- `lake env lean Tests/Chapter_34_CookLevin_MainTheorem.lean`: passed;
- `lake build
  CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.MainTheorem`:
  passed, `3607/3607` jobs;
- `lake build CLRSLean.Chapter_34`: passed, `3674/3674` jobs;
- `lake build CLRSLean`: passed, `9917/9917` jobs;
- `python3 scripts/check_repository.py`: passed, including progress, status,
  literate-site, placeholder, and local-link policies;
- `git diff --check`: passed.

Both Chapter 34 interface tests report only the standard Mathlib foundations
`propext`, `Classical.choice`, and `Quot.sound` for the audited main theorems.
No project-local axiom or proof hole is introduced by this checkpoint.

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
