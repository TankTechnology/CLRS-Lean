# Chapter 34 Cook--Levin Closure

Date: 2026-08-21

> **Historical checkpoint.** Cook--Levin remains closed, and the remaining
> Chapter 34 work recorded below was completed by 2026-08-25. Chapter 34 is now
> `main-proof-complete` at its advertised textbook boundary.

## Scope and result

This checkpoint closes the textbook Cook--Levin theorem in the repository's
concrete two-tape Turing-machine complexity model.  It does not identify a
polynomial output-length function with a polynomial-time reduction: a fixed
TM2 is proved to compute the complete circuit encoding directly from the
original input within a polynomial step bound.

The public theorem layer now contains:

- `Turing.CookLevin.cookLevinMap_polyTimeComputable`, the concrete
  polynomial-time computation of the exact map;
- `Turing.CookLevin.cookLevin_theorem`, the universal reduction from every
  language in `ClassNP` to `GeneralCircuitSAT`;
- `Turing.CookLevin.generalCircuitSAT_npHard`;
- `Turing.CookLevin.generalCircuitSAT_npComplete`.

The semantic and size foundations remain exposed independently through the
whole-tableau circuit theorems and `cookLevin_textbookCircuitization`.

## Implementation checkpoints

- `f7318a27` closes the concrete verifier-body compiler.
- `91381f21` adds a reusable fixed finite-output pair codec and same-input
  polynomial-time concatenation layer.
- `175af7e2` closes the complete Cook--Levin map compiler.
- `ba672da5` proves and exports the main reduction, NP-hardness, and
  NP-completeness theorems.

The large construction is split across small source files so focused Lean
checks do not require editing and recompiling one monolithic proof file.

## Verification

The following acceptance checks pass at this checkpoint:

```text
lake env lean Tests/Chapter_34_CookLevin_MainTheorem.lean
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin
lake build CLRSLean.Chapter_34
python3 scripts/check_repository.py
```

The focused axiom audit reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` dependencies for the map compiler, the
universal Cook--Levin theorem, and `GeneralCircuitSAT` NP-completeness.  It
does not report `sorryAx` or a project-specific axiom.

The repository-wide policy suite also passes, including progress/dashboard
consistency, edition-map and book-coverage checks, the complete Chapter 34
source inventory and literate navigation, placeholder scanning, and local
Markdown-link validation.  The 658 Chapter 34 proof files are intentionally
kept as small compilation units and are all registered in the public source
catalog rather than being collapsed into a monolithic Lean file.

## Honest remaining Chapter 34 boundary

Cook--Levin itself is no longer an open Chapter 34 item.  The chapter remains
partial because its current `CLIQUE` target is the specialized occurrence
graph used by the existing 3-CNF reduction, rather than the textbook general
graph-plus-`k` decision problem, and Section 34.5's NP-complete-problem
reduction chain is not yet represented.
