# Book Progress, Site, and Proof Hardening Design

Date: 2026-08-26

## Scope

This pass is deliberately conservative.  It does not redesign the Verso site,
change the deployment architecture, or broaden the advertised project boundary.
It makes the current proof state easier to read, repairs one mobile navigation
defect, and closes one concrete textbook-level refinement gap in a small Lean
module.

## Audited state

- The canonical fourth-edition ledger has 35 chapter rows: 34 are
  `main-proof-complete` and Chapter 1 is `expository`.
- All 1,609 selected reader-facing theorem entries are proved, with zero
  edition-coverage gap units.  The separate online-material ledger contains 465
  entries.
- The Lean-native flagship trust gate covers Chapters 1--35 and accepts only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The deployed site is live and its directly fetched HTML is current.  A search
  crawler can still return a month-old copy of the homepage; this is an external
  indexing cache, not a repository or Pages failure.

## Website findings

1. The homepage explains the fourth-edition migration accurately, but does not
   expose the current 35/35 and 1,609/1,609 snapshot near the start.
2. The Progress page opens with a maintainer regeneration command and a long
   compatibility explanation before its most useful reader facts.
3. On a 390-pixel viewport, the current-page breadcrumb competes with the search
   box and is visibly clipped.  The page itself has no horizontal overflow and
   produces no browser-console errors.
4. The Status page gives Chapter 34 much more visual weight than the whole-book
   state, so a reader can mistake a flagship detail report for the global
   summary.
5. The chapter matrix is a horizontally scrollable preformatted block.  Replacing
   it with a richer component would be a redesign, so it is recorded but deferred
   in this basic pass.

## Minimal repair

- Add a concise, scope-qualified whole-book snapshot to the landing page.
- Make the generated Progress opening reader-facing and keep regeneration
  instructions in its maintainer section.
- Add a concise whole-book summary before the Chapter 34 detail on Status, and
  shorten duplicated Chapter 34 prose where existing chapter pages already own
  the detail.
- At mobile width, keep the root breadcrumb but hide an additional current-page
  crumb and its separator.  Do not change desktop navigation or page layout.

## Proof hardening target

Chapter 6 already proves array-level maximum, increase-key, extract-max, and
delete.  The remaining asymmetric textbook operation is array-level
`MAX-HEAP-INSERT`.

The new small module will:

1. append the new key as the last heap cell;
2. prove that the resulting array satisfies `ArrayMaxHeapExceptUp`, with the
   only possible violation on the new cell's incoming edge;
3. reuse `ArrayMaxHeapExceptUp.bubbleUpFuel_global` to restore the global heap;
4. prove backing-list length and permutation specifications; and
5. expose the declarations through focused interface checks.

Explicit RAM costs and a sharp logarithmic step counter remain outside this
pass.

## Verification

- Python tests must fail before each website behavior change and pass after it.
- The new Chapter 6 interface check must first fail on the missing declarations.
- Build only the affected Lean modules and focused interface tests during
  development.
- Before completion, run the repository checks, the Lean-native trust gate, the
  incremental library build, site rendering checks, and desktop/mobile browser
  regression checks.

