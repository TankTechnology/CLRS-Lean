# Fourth-edition status-ledger reconciliation design

Date: 2026-08-06

Status: approved for autonomous implementation

## Problem

The fourth-edition structural migration intentionally initialized section
coverage conservatively.  The README chapter table is generated from
`docs/clrs-proof-progress.csv`, while `scripts/check_progress_csv.py` requires
the chapter status to be `partial` whenever any canonical section in
`docs/clrs-fourth-edition-map.csv` is `partial` or `not-started`.

That rule is sound, but two different facts are currently easy to confuse:

1. every theorem selected by the progress ledger is kernel checked; and
2. a chapter may still omit one or more central fourth-edition section
   obligations.

In addition, some conservative `partial` section rows may be stale relative to
the theorem-bearing source and `docs/proof-map.md`.  The status ledger therefore
needs an evidence-based reconciliation rather than a blanket promotion of all
chapters whose tracked theorem count is complete.

## Goals

1. Audit the currently suspect fourth-edition mappings for Chapters 3, 13, 14,
   17, and 29 against actual theorem declarations.
2. Promote a section from `partial` to `facade` only when the current
   compatibility source covers its central fourth-edition obligations at the
   repository's stated abstraction level.
3. Preserve `partial` for real coverage gaps and replace generic notes with
   exact missing obligations.
4. Make the README distinguish theorem-proof completion from edition-section
   coverage without weakening the conservative chapter roll-up rule.
5. Keep the map, progress ledger, generated README table, progress page, status
   page, and fourth-edition chapter guides consistent.

## Non-goals

- Do not add new algorithm formalizations in this reconciliation.
- Do not mark a section complete merely because related definitions or
  implementation fragments exist.
- Do not require pointer-level, mutable-array, or RAM-cost refinements when the
  repository explicitly claims only a mathematical or pure-functional model;
  those refinements remain documented future work.
- Do not promote known gaps in Chapters 4, 7, 10, 11, 15, or 32.
- Do not change the compatibility or deprecation schedule.

## Completion rule

For each audited section, the evidence table records:

- the central fourth-edition algorithm or mathematical object;
- the semantic or representation invariant;
- the principal correctness, optimality, structural, or asymptotic theorem;
- executable behavior where the repository claims an implementation;
- the theorem declaration and source location that discharges each obligation;
- any remaining central obligation.

The section state is chosen as follows:

- `facade`: an existing legacy source discharges the central obligations at the
  documented abstraction level, although names and paths have not yet been
  migrated;
- `partial`: some central obligation remains open;
- `not-started`: no canonical theorem-bearing source represents the section.

Optional refinements do not by themselves force `partial`, but must be named in
the coverage note or proof map.  Examples include a pointer-memory refinement
when the canonical result is already proved for a pure tree, or an additional
monoid generalization beyond a proved augmentation theorem.  In contrast,
missing algorithm correctness, preservation, optimality, or the section's main
bound is a central gap and forces `partial`.

## Audited scope and expected disposition

The implementation begins from these hypotheses, which must be confirmed from
source before any state change:

| Fourth-edition chapter | Initial hypothesis |
| --- | --- |
| 3, Characterizing Running Times | §§3.1--3.2 may be stale `partial` rows because the proof map reports their formal definitions and main closure properties complete. |
| 13, Red-Black Trees | §§13.3--13.4 may be stale if insertion/deletion semantics and red-black preservation are both theorem-backed; a structure-only deletion theorem is insufficient. |
| 14, Dynamic Programming | §14.3 remains `partial` unless the generic dynamic-programming principles, not only the four worked algorithms, are formally represented. |
| 17, Augmenting Data Structures | §17.2 may be stale if the generic augmentation theorem and update preservation are present; an optional monoid refinement does not force `partial`. |
| 29, Linear Programming | §§29.1--29.3 may be stale if formulation, feasibility/optimality, and duality are complete in the finite real-matrix model; detailed simplex material moved online is not counted as a main-text gap. |

The audit may reject any hypothesis.  The final state follows declarations, not
the chapter guide's prose or the desired number of green badges.

## README status model

The generated README keeps the proved-count fraction and chapter coverage badge
as separate signals:

- `proved / tracked` means that every theorem intentionally listed for that
  chapter is kernel checked;
- `partial coverage` means that the fourth-edition map still lists at least one
  central section obligation as partial or not started;
- `facade` in the edition map means proof content is currently supplied through
  a legacy import during the compatibility window.

The table legend and nearby prose must state that `1326 / 1326` is not a claim
of complete fourth-edition coverage.  Partial rows should expose a short exact
gap in the existing remaining-work column rather than a generic warning.

The chapter ledger calls its aggregate `edition_gap_units`: each unresolved
section in a represented chapter contributes one unit, while a wholly
unrepresented chapter contributes one aggregate whole-chapter unit.  This is a
coverage metric, not a count of missing theorem declarations.

## Sources of truth and generated files

Manual evidence and status changes belong in:

- `docs/clrs-fourth-edition-map.csv` for section coverage;
- `docs/proof-map.md` for theorem-level evidence and exact gaps;
- relevant `CLRSLean/FourthEdition/Chapter_NN.lean` and legacy chapter guides
  when their prose is stale;
- `docs/clrs-proof-progress.csv` for the resulting chapter-level summary.

README and progress/status views are regenerated with repository scripts.  No
generated file is hand-edited when a generator owns it.

## Parallel execution

Three read-only audits run independently:

1. Chapters 3 and 13;
2. Chapters 17 and 29;
3. Chapter 14 plus README terminology.

The primary task integrates all results into the shared ledgers, checks theorem
names and locations directly, and performs all writes.  This avoids concurrent
edits to the same CSV and generated documentation.

## Verification

The reconciliation is accepted only after:

1. focused map/progress/generator tests pass;
2. `scripts/check_repository.py` passes;
3. every referenced theorem name resolves in source and the affected Lean
   modules build;
4. generated files are up to date;
5. README chapter statuses agree with the edition map's conservative roll-up;
6. `git diff --check` reports no formatting errors;
7. a final independent review finds no unsupported promotion.

A full website render is not required because this change does not alter the
renderer or literate module graph.  The lightweight site/content validation in
the repository check is required; this preserves the earlier deployment-speed
policy while still catching stale generated metadata.
