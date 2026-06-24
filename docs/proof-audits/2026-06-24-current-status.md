# Current Proof-Status Audit

Date: 2026-06-24

This audit records evidence about whether the current chapter status claims are
honest and where the next proof work should go.  It is intentionally scoped to
the imported CLRS-Lean source, not experimental worktrees.

## Checks Run

- Imported Lean files inspected: `CLRSLean/**/*.lean`.
- Unfinished-proof marker search:
  `rg -n '\b(sorry|admit|axiom)\b' CLRSLean -g '*.lean'`.
- Result: no imported theorem file contains an unfinished proof marker.  The
  only previous match was expository prose in Chapter 1; that prose has been
  corrected to match the no-`sorry` imported-source policy.

## Status Honesty

- Sections marked `proved` currently have named Lean theorems and no imported
  `sorry`/`admit`/`axiom` markers.
- Sections marked `partial` expose the missing mathematical or modeling layer:
  probability for chained hashing, pointer navigation/transplant for BSTs, full fixup
  algorithms for red-black trees, sorted-order/certificate automation for
  greedy and MST algorithms.
- The MST and activity-selection theorems remain intentionally certificate
  based.  They are useful but should not be described as full textbook proofs
  until the certificates are derived from the algorithmic hypotheses.

## Progress This Pass

- Chapter 13 now has a bundled local invariant predicate,
  `CLRS.Chapter13.RBTree.RedBlackShape`.
- The theorem `CLRS.Chapter13.RBTree.redBlackShape_repaint_black` proves that
  repainting the root black establishes the bundled root-black/no-red-red/
  balanced-black-height shape invariant from the two non-root invariants.
- Chapter 12 now proves functional successor/predecessor queries:
  `CLRS.Chapter12.BSTree.successor?_least_greater` and
  `CLRS.Chapter12.BSTree.predecessor?_greatest_less`.
- Chapter 12 now proves functional deletion:
  `CLRS.Chapter12.BSTree.inTree_delete_iff` and
  `CLRS.Chapter12.BSTree.delete_ordered`.

## Next Proof Priorities

1. Chapter 16.1: derive the activity-selection exchange certificate and
   maximum-cardinality theorem for `greedySelect`; the sorted head/min-finish
   and executable sublist/feasibility layers are now proved.
2. Chapter 23.2: add the sorted-prefix invariant needed to turn Kruskal's edge
   order into lightness certificates.
3. Chapter 4.1: connect the CLRS divide-and-conquer maximum-subarray pseudocode
   to the proved exhaustive-search specification.
4. Chapter 12.1: design a parent-pointer/transplant refinement for the current
   functional tree theorem.

## Audit Rule

Do not move a section from `partial` to `proved` unless the corresponding
textbook-level theorem is both stated and proved in imported Lean source without
external certificates that encode the missing algorithmic step.
