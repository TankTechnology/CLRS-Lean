# CLRS-Lean Documentation

Start with the [book website](https://tanktechnology.github.io/CLRS-Lean/) to
read the formalization. This index connects readers and contributors to the
maintained sources behind it.

## Read and verify

| I want to… | Start here |
| --- | --- |
| Browse the 35 chapters | [Chapter index](https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/) |
| Understand what “complete” means | [Project scope](scope.md) and [Proof Status](../src/CLRSLean/Status.lean) |
| Check chapter coverage | [Progress Dashboard](../src/CLRSLean/Progress.lean), generated from the [chapter ledger](clrs-proof-progress.csv) |
| Find exact theorem statements | [Chapter guides](../src/CLRSLean/FourthEdition/) and [interface tests](../tests/) |
| Check proof trust | [Trust-gate guide](audits/v1-trust-gate.md) and [chapter audits](audits/index.md) |
| Announce the milestone | [Release announcement](releases/2026-09-08-announcement.md) |

## Contribute and maintain

| Task | Guide |
| --- | --- |
| Set up the library | [README](../README.md#local-setup) |
| Develop and verify proofs | [Chapter workflow](workflows/chapter-workflow.md) and [fast verification](workflows/lean-fast-verification.md) |
| Review a chapter's completion | [Completion checklist](workflows/chapter-completion-audit.md) |
| Understand code ownership and naming | [Repository architecture](repository-architecture.md) |
| Resolve third- and fourth-edition numbering | [Migration guide](migrations/clrs4.md) and [edition map](clrs-fourth-edition-map.csv) |
| Build, preview, or publish the website | [Site architecture and runbook](site-architecture.md) |
| Prepare isolated builds | [Build and agent infrastructure](build-and-agents.md) |
| Follow the chapter audit repairs | [Repair queue and local evidence](plans/2026-09-08-chapter-repairs/index.md) · [GitHub tracker #376](https://github.com/TankTechnology/CLRS-Lean/issues/376) |
| Find future work | [GitHub issues](https://github.com/TankTechnology/CLRS-Lean/issues) |

## Document directories

- `workflows/`: repeatable contributor and verification procedures.
- `audits/`: dated evidence and the trust-gate guide. Historical findings describe
  the source at audit time; the repair queue tracks subsequent evidence. The
  current ledger's labels are still being reconciled with the September 8 findings.
- `proof-patterns/`: reusable proof techniques and engineering lessons.
- `designs/`: dated design decisions and specifications.
- `plans/`: dated implementation plans, retained as development history.
- `research/`: research contracts and exploratory notes beyond the main book.
- `releases/`: public announcement drafts and release evidence.
- `migrations/`: compatibility and source-migration policies.
- `literate/`: the website stylesheet.

The chapter ledger, [online-material ledger](clrs-online-material.csv), and
edition map remain the machine-readable inventory sources. Their counts and
labels do not override known semantic findings; the audit and linked issues
record the original obligations; the repair queue records subsequent fixes and
verification.
