# Project Scope

CLRS-Lean formalizes a selected theorem stack spanning all 35 chapters of
*Introduction to Algorithms*, fourth edition.  “Represented” means that a
chapter has checked Lean definitions and theorems for its selected main-text
material; it does not mean that every paragraph, exercise, problem, or machine
model in the book has been reproduced.

## Included in the advertised boundary

- mathematically meaningful definitions and executable reference models;
- correctness, structural, and asymptotic theorems selected for each represented
  section;
- explicit assumptions at public theorem boundaries;
- interface tests that keep important names and theorem signatures stable;
- a separate ledger for relevant online-material chapters and sections.

The exact checked boundary is the Lean source itself.  The chapter and section
aggregators, together with `tests/*_Interface.lean`, are the most precise public
index.  The two progress CSV files summarize that boundary for readers and for
the generated website.

## Not claimed by default

Unless a source module says otherwise, project completion does not claim:

- every exercise, end-of-chapter problem, historical note, or worked example;
- a line-by-line transcription of textbook pseudocode;
- pointer identity, allocation, mutation, cache, word-RAM, distributed-system,
  hardware, or operating-system behavior;
- floating-point or numerical-error analysis where the formal model uses exact
  arithmetic;
- executable performance matching the textbook implementation;
- removal of Lean's standard logical axioms such as classical choice and
  quotient soundness.

These exclusions keep theorem statements honest: an abstract cost model proves
facts about that model, not automatically about a concrete machine.

## Status and future work

- [`clrs-proof-progress.csv`](clrs-proof-progress.csv) is the canonical
  fourth-edition coverage ledger.
- [`clrs-online-material.csv`](clrs-online-material.csv) is the
  canonical online-material ledger.
- `src/CLRSLean/Status.lean` gives a concise human-readable overview.
- Open enhancements and deliberately deferred work belong in
  [GitHub issues](https://github.com/TankTechnology/CLRS-Lean/issues), where ownership,
  discussion, and closure remain visible.

Dated audit reports are evidence for the commit they name.  They are not live
project dashboards and should not be edited whenever coverage changes.

## Describing the current milestone

The inventory records 1,689 proved selected entries across 35 chapter guides,
with Chapter 1 expository, and 470 separately tracked supplementary entries.
These are inventory facts. The [September 8 semantic review](audits/2026-09-08-chapter-review/index.md)
identified source-level interface and implementation defects and unsupported
execution-cost claims. The [dated repair record](plans/2026-09-08-chapter-repairs/index.md)
tracks subsequent source fixes, verification, and integration separately from
the immutable audit snapshot.

The ledger labels 34 theorem-bearing chapters `main-proof-complete` within
their explicitly described models and records zero edition-gap units. The
repair work updates section notes and evidence without inflating the selected
inventory count. These labels describe the ledger's scope; they do not certify
all textbook statements, exercises, implementation models, or an independent
page-by-page comparison with the book.

Algorithm interfaces must be inhabitable on their intended domain, updates
must satisfy their stated semantics, and execution-cost claims must name their
counted operations and connect to that execution. Mathematical or charged-cost
models do not automatically establish persistent-data-structure, RAM,
floating-point, or bit-complexity bounds. Chapter guides and section notes name
these boundaries, including the places where an old budget remains an
analytical reference alongside a newly costed execution.

Public wording should describe the selected formalization and chapter-repair
milestone and link its scope and verification. Local build results do not imply
that a website has been deployed or that a social-media announcement was posted.
