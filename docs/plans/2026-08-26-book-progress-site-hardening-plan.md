# Book Progress, Site, and Proof Hardening Implementation Plan

> Execute this plan in the existing clean integration worktree.  Keep proof and
> site changes in separately reviewable commits and do not push without explicit
> authorization.

**Goal:** Make the deployed book state easier to verify and add the missing
array-level Chapter 6 heap insertion proof without redesigning the site.

**Architecture:** The CSV remains the progress source of truth, the Progress
page remains generated, and Verso remains the only frontend.  The proof extends
the existing array heap interface through a child module that imports and reuses
the established upward-bubbling invariant.

**Technology:** Lean 4, Mathlib, Python `unittest`, Verso literate HTML, CSS,
Playwright.

## Task 1: Reader-facing progress facts

1. Extend `scripts/test_check_progress_csv.py` with failing assertions for the
   reader-first generated opening.
2. Add a failing source-contract test for the landing/status whole-book facts.
3. Update `scripts/check_progress_csv.py`, regenerate `CLRSLean/Progress.lean`,
   and minimally edit `CLRSLean.lean` and `CLRSLean/Status.lean`.
4. Run the focused Python tests and compile the three affected Lean pages.

## Task 2: Mobile breadcrumb regression

1. Add a failing stylesheet contract test for the narrow-screen breadcrumb
   policy.
2. Add the minimal media-query rules to `docs/literate/clrs-literate.css`.
3. Reassemble the site from current rendered HTML and verify desktop/mobile DOM,
   overflow, console output, and screenshots with Playwright.

## Task 3: Array-level MAX-HEAP-INSERT

1. Add `Tests/Chapter_06_Heap_Insert_Interface.lean` with checks for the proposed
   definition, upward-exception lemma, and state-correctness theorem; confirm the
   test fails because the declarations do not exist.
2. Add
   `CLRSLean/FourthEdition/Chapter_06/Section_06_5_Priority_Queues/Insert.lean`.
3. Prove the append-only-upward-exception lemma, define insertion by reusing the
   existing bubble loop, and prove heap, length, and permutation correctness.
4. Import and link the child module from the Chapter 6 guide and register it in
   `literate.toml` without adding a new top-level sidebar row.
5. Run the focused Lean test and Chapter 6 interface build.

## Task 4: Records and verification

1. Update the Chapter 6 progress note and selected theorem count only if the new
   declarations are promoted into the reader-facing inventory; regenerate the
   dashboard in the same commit.
2. Run repository checks, trust gate, incremental `lake build CLRSLean`, the site
   preparation/rendering checks, and final Playwright checks.
3. Report commits and remaining deferred issues.  Do not push unless requested.

