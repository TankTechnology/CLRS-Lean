# Semantic-Fidelity Audit Index

These reports are immutable snapshots of the repository at the stated date.
They are evidence records rather than the live completion ledger.

## Whole-book audits

- [September 8 fourth-edition chapter review](2026-09-08-chapter-review/index.md)
  covers all 35 chapters and 137 mapped section entries. It reviews definitions,
  public theorems, selected proof dependencies, and independent cross-review.
  It also includes reproducible source-level counterexamples.
- [August 28 whole-book proof-gap audit](2026-08-28-whole-book-proof-gap-audit.md)
  reviews algorithm semantics, correctness and invariants, optimality or lower
  bounds, cost attachment, model provenance, and public evidence.

All textbook-equivalence judgments in these audits are marked
`NOT-INDEPENDENTLY-VERIFIED`: the textbook was not checked independently page by
page. Source-level defects and kernel-checked counterexamples remain directly
verifiable.

## Consolidated earlier chapter snapshots

Earlier standalone audits for Chapters 2, 3, 4, 5, 6, and 15 were consolidated
after the September 8 whole-book review superseded them. Their recorded verdicts
were:

| Chapter | Audit date | Verdict distribution | Recorded defects |
| --- | --- | --- | --- |
| 2 | 2026-08-27 | MATCH 24, MINOR 10 | 10 MINOR |
| 3 | 2026-08-27 | MATCH 59 | none |
| 4 | 2026-08-18 | MATCH 57, MINOR 13 | 13 MINOR |
| 5 | 2026-08-18 | MATCH 21, MINOR 15, MAJOR 1, UNCERTAIN 1 | 1 MAJOR, 15 MINOR |
| 6 | 2026-08-27 | MATCH 39, MINOR 12, MAJOR 2 | 2 MAJOR, 12 MINOR |
| 15 | 2026-08-17; closure review 2026-08-27 | MATCH 48 | none |

The complete original snapshots remain recoverable from Git history. Current
claims are governed by [`docs/clrs-proof-progress.csv`](../clrs-proof-progress.csv),
the [trust-gate record](v1-trust-gate.md), and the September 8 repair evidence.
