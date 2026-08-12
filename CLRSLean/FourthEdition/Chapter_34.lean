import CLRSLean.Chapter_34

/-!
# Chapter 34 — NP-Completeness

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

The current Chapter 34 guide imports {lit}`CLRSLean.Chapter_34`, which supplies
Sections 34.1 (framework and closure properties), 34.2 (verification / `P ⊆ NP`),
34.3 (reducibility / transitivity of `≤_P`), and 34.4 (the specific reductions
`CIRCUIT-SAT ≤_P SAT` and `3-CNF-SAT ≤_P CLIQUE`, plus the SAT → 3-CNF-SAT
semantic core).

## Coverage boundary

Status: partial.  The theorem layer is complete — polytime composition,
`P ⊆ NP`, transitivity of `≤_P`, and the closure of `P` under complement,
union, and intersection — and the §34.4 reductions `CIRCUIT-SAT ≤_P SAT`
(Lemma 34.6) and `3-CNF-SAT ≤_P CLIQUE` (Lemma 34.10) are proved.  The
assembled `SAT ≤_P 3-CNF-SAT` machine reduction and Section 34.5 (NP-complete
problems) are not yet represented.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
