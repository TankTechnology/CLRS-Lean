# CLRS-Lean Documentation

This directory contains the small set of documents that complement the Lean
sources.  The source tree and its interface tests remain the authority for
theorems; documentation should explain scope, architecture, and reusable proof
techniques instead of duplicating theorem declarations.

## Start here

| Question | Canonical source |
| --- | --- |
| What does the project claim to cover? | [`scope.md`](scope.md) |
| Which chapters and sections are represented? | [`clrs-proof-progress.csv`](clrs-proof-progress.csv) and [`clrs-online-material.csv`](clrs-online-material.csv) |
| What is the current high-level status? | [`../CLRSLean/Status.lean`](../CLRSLean/Status.lean) and the generated [`../CLRSLean/Progress.lean`](../CLRSLean/Progress.lean) |
| Where are exact theorem names checked? | The relevant `CLRSLean/Chapter_*` modules and `Tests/*_Interface.lean` |
| What remains to be done? | [Open GitHub issues](https://github.com/TankTechnology/CLRS-Lean/issues) |

## Maintainer guides

- [`repository-architecture.md`](repository-architecture.md) explains ownership
  and change boundaries.
- [`migrations/clrs4.md`](migrations/clrs4.md) records the fourth-edition mapping
  contract.
- [`site-architecture.md`](site-architecture.md) and
  [`workflows/chapter-workflow.md`](workflows/chapter-workflow.md) cover publishing
  and chapter work.
- [`build-and-agents.md`](build-and-agents.md) documents local verification.

## Reusable records

- [`proof-patterns/`](proof-patterns/) contains durable proof-engineering lessons.
- [`audits/`](audits/) contains semantic audit artifacts.  Treat dated reports as
  immutable snapshots, not as live status ledgers.
- [`proof-audits/chapter-completion-audit.md`](proof-audits/chapter-completion-audit.md)
  is the reusable chapter-completion checklist.
- [`research/`](research/) contains research-facing methodology notes.

Historical implementation plans, checkpoint reports, and retired status boards
remain recoverable from Git history.  They are intentionally not maintained on
`main`.
