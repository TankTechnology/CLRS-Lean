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
aggregators, together with `Tests/*_Interface.lean`, are the most precise public
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
- `CLRSLean/Status.lean` gives a concise human-readable overview.
- Open enhancements and deliberately deferred work belong in
  [GitHub issues](https://github.com/TankTechnology/CLRS-Lean/issues), where ownership,
  discussion, and closure remain visible.

Dated audit reports are evidence for the commit they name.  They are not live
project dashboards and should not be edited whenever coverage changes.
