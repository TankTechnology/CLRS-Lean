import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs

/-!
# 34.4 NP-Completeness Proofs

This reader page presents Cook--Levin and the first concrete NP-completeness
reductions in the textbook chain.

## Main results

- Cook--Levin reduces every NP language to general circuit satisfiability.
- {lit}`CIRCUIT-SAT ≤_P SAT ≤_P 3-CNF-SAT ≤_P CLIQUE`.
- SAT and 3-CNF-SAT have total raw assignment checkers with linear certificate
  bounds, fixed reduction-backed verifier machines, and standalone
  NP-completeness theorems.
- General circuit satisfiability and the public graph-plus-{lit}`k` CLIQUE
  language are NP-complete.

## Implementation source

See [the complete theorem-bearing source](CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/).
-/
