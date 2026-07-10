import CLRSLean.Chapter_02

/-!
# Workflow

CLRS-Lean uses a repeatable section workflow.  The goal is to make future
chapters easy to audit, easy to deploy, and pleasant to read.

## Section Lifecycle

1. Textbook map.
2. Algorithm model.
3. Mathematical proof plan.
4. Lean theorem interface.
5. Lean proof.
6. Verification.
7. Progress and documentation update.
8. Repository and site verification.

## 1. Textbook Map

Record the section number, algorithm, main theorem-like claims, proof method,
and any exercises or chapter-end problems.  Exercises are normally marked
{lit}`future-work` until the main theorem interface is stable.

## 2. Algorithm Model

Choose the Lean model that exposes the proof cleanly.  Prefer a mathematical
model first: lists for sorting, finite sets for edge collections, abstract
oracles for cycle tests, and recurrence functions for first-pass runtime
arguments.

Implementation-level refinements such as arrays, heaps, priority queues, and
union-find can refine the mathematical model later.

## 3. Mathematical Proof Plan

Write the proof as small claims before proving them in Lean.  Typical patterns
include:

* sortedness plus permutation preservation;
* loop invariant over a state relation;
* exchange argument;
* cut property;
* recurrence solution;
* optimal-substructure lower bound.

## 4. Lean Interface

Expose theorem names that a reader would search for.  A section should have a
small public surface even if the local proof needs many helper lemmas.

Example:

```lean
#check CLRS.Chapter02.insertionSort_sorted
#check CLRS.Chapter02.insertionSort_perm
```

## 5. Lean Proof

Keep early proofs local and readable.  Extract shared abstractions only after at
least two sections need the same interface.  This keeps the site from developing
premature infrastructure that readers must understand before they can read a
single algorithm.

## 6. Verification

Use narrow checks while editing, then a project-level build before publishing:

* {lit}`lake env lean CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean`
* {lit}`lake env lean Tests/Chapter_02_Interface.lean`
* {lit}`lake build`
* {lit}`lake build :literateHtml`

When local {lit}`literateHtml` generation is too slow, the Lean build and static
configuration checks still provide useful evidence, and the GitHub Pages build
becomes the final deployment gate.

## 7. Progress And Documentation Update

Every user-facing section change should update the book structure:

* the relevant {lit}`CLRSLean/Chapter_XX.lean` chapter page;
* {lit}`literate.toml` if a new module should appear in the navigation;
* {lit}`docs/proof-map.md` for the longer maintainer ledger;
* {lit}`docs/clrs-proof-progress.csv` when chapter coverage changes;
* {lit}`docs/proof-status-board.md` only when planning priorities change.

## 8. Progress CSV Update

The proof-progress CSV is the machine-readable ledger for agents and the public
dashboard.  Any agent that changes reader-facing theorem coverage should update
{lit}`docs/clrs-proof-progress.csv` in the same commit.

Rule of thumb:

* new public theorem group: increment {lit}`tracked_key_theorems` and
  {lit}`proved_tracked_theorems`;
* closed gap: reduce {lit}`missing_core_groups`, update {lit}`repo_status`, and
  move the item from {lit}`remaining_core_groups` to
  {lit}`proved_key_theorem_groups`;
* new chapter or section page: update {lit}`represented_sections`,
  {lit}`evidence_source`, {lit}`literate.toml`, and the chapter guide page;
* deferred or blocked theorem group: record it in {lit}`remaining_core_groups`
  instead of silently dropping it.

Regenerate the dashboard after changing the CSV:

* {lit}`uv run python scripts/check_progress_csv.py --write-dashboard`

## 8. Repository And Site Verification

Before committing proof-status changes, run:

* {lit}`uv run python scripts/check_repository.py`
* {lit}`lake build CLRSLean`

When navigation or reader-facing prose changes, also run
{lit}`lake build :literateHtml` and the generated-site checks.
-/
