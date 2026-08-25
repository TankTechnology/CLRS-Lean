# Chapter 34 Remote Checkpoint

Date: 2026-08-19

> **Historical checkpoint.** Superseded on 2026-08-25: Chapter 34 is now
> `main-proof-complete` at its advertised textbook boundary. The branch and
> remaining-work statements below record repository state on the date above.

## Repository state

- Working branch: `codex/ch34-textbook-closure`.
- Verified pre-audit code head: `fd96e1ccf3adc1a84a360bf6e16c667a129e1404`.
- The GitHub branch head matched that commit exactly before this documentation
  cleanup.
- The feature branch was 79 commits ahead of `origin/main` and had not been
  merged into `main`.
- Relative to `origin/main`, the branch changed 194 files: 92 Chapter 34 source
  files, 74 Chapter 34 tests, and 22 documentation files, with 39,654 insertions
  and 160 deletions.

## Textbook-facing results already closed

- Sections 34.1--34.3 provide the polynomial-time, NP-verification, and
  polynomial-reduction framework, including `P ⊆ NP` and reduction
  transitivity.
- The represented reductions `CIRCUIT-SAT ≤_P SAT`, `SAT ≤_P 3-CNF-SAT`, and
  `3-CNF-SAT ≤_P` occurrence-`CLIQUE` have concrete machines.
- The semantic Cook--Levin tableau circuit is well formed and exact, with
  polynomial gate-count, input-count, and complete encoding-length bounds.
- `cookLevin_textbookCircuitization` packages the explicit function-level map,
  exact language semantics, and polynomial output length without overstating
  polynomial-time computability.
- `generalCircuitSAT_mem_ClassNP` is closed through a concrete certificate
  checker TM2 whose successful, rejecting, and malformed routes share an
  explicit polynomial runtime bound.

## Concrete generator progress

- The header/input/pool, validity, transition, boundary, and final-conjunction
  gate streams have exact semantic targets.
- The complete script-consuming verifier body and post-transition tail run
  continuously and have polynomial script-time bounds.
- The raw-input validity compiler now provides row seeds, halted operands,
  structured one-hot source families, and runtime-height stack/cell source
  families.
- `arithmeticFinalConjunctionWires_eq_semantic` identifies the closed arithmetic
  final-conjunction wire list with the semantic constraint list.
- `arithmeticRawOneHotOutputFamilySource_runToFinish` computes the raw one-hot
  output-wire segment continuously; its quadratic bound is
  `arithmeticRawOneHotOutputFamilySource_steps_le`.

## Exact remaining boundary

1. Complete the validity-tail source by joining raw one-hot outputs, the halted
   output, reverse stack/cell outputs, the final conjunction start, and the
   required delimiters.
2. Interleave the row fragments and prove the complete validity-row input is
   generated in polynomial time from the original input.
3. Compile transition-family and verifier-tail scripts from the original input,
   then compose them with the already verified script-consuming body.
4. Package the resulting TM2 as polynomial-time computation of `cookLevinMap`;
   only then close standard `NPHard GeneralCircuitSAT` and
   `NPComplete GeneralCircuitSAT`.
5. Represent general graph-plus-`k` `CLIQUE` and the Section 34.5 chain.

## Fresh verification

- Focused tests for the one-frame output source, output-family source,
  validity-row tail operands, textbook Cook--Levin interface, and
  GeneralCircuitSAT verifier runtime all passed.
- `lake build CLRSLean.Chapter_34` completed successfully: 3212 jobs.
- The checked headline theorems depend only on the repository's standard
  `propext`, `Classical.choice`, and `Quot.sound` axiom surface.
- No declaration-level `sorry`, `admit`, or custom `axiom` occurs under
  `CLRSLean/Chapter_34`.
- The Chapter 34 navigation and source inventory pass the repository's site
  consistency check.  The full repository checker still stops in two inherited,
  non-Chapter-34 reader-link tests for Chapter 5 `OnlineHiring` and Chapter 7
  `Comparison_Probability`; neither failure is introduced or modified by this
  checkpoint.

This checkpoint deliberately records Chapter 34 as partial: it does not claim
the concrete Cook--Levin generator, NP-hardness, general `CLIQUE`, or Section
34.5 before their named Lean theorems exist.
