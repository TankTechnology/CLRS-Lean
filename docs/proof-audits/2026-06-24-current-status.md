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
- Chapter 13 now also proves red-red local repair certificates:
  `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`,
  `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`,
  `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`, and
  `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`.
- Chapter 12 now proves functional successor/predecessor queries:
  `CLRS.Chapter12.BSTree.successor?_least_greater` and
  `CLRS.Chapter12.BSTree.predecessor?_greatest_less`.
- Chapter 12 now proves functional deletion:
  `CLRS.Chapter12.BSTree.inTree_delete_iff` and
  `CLRS.Chapter12.BSTree.delete_ordered`.
- Chapter 3.2 now proves additional standard-function comparisons:
  `CLRS.Chapter03.isLittleO_pow_const_exp`,
  `CLRS.Chapter03.isLittleO_log_rpow`, and
  `CLRS.Chapter03.isLittleO_exp_exp_of_lt`.
- Chapter 3.2 now also proves harmonic-number growth:
  `CLRS.Chapter03.isEquivalent_harmonic_log` and
  `CLRS.Chapter03.isBigTheta_harmonic_log`.
- Chapter 3.2 now proves the factorial table layer more directly:
  `CLRS.Chapter03.factorial_lower_bound_offset`,
  `CLRS.Chapter03.factorial_lower_bound_half_pow`, and
  `CLRS.Chapter03.isLittleO_factorial_pow_self`.
- Chapter 3.2 now also proves half-scale floor/ceiling Θ wrappers:
  `CLRS.Chapter03.isBigTheta_nat_floor_half_coerce` and
  `CLRS.Chapter03.isBigTheta_nat_ceil_half_coerce`.
- Chapter 5.1 now connects the hiring-problem expectation theorem to
  logarithmic growth:
  `CLRS.Chapter05.harmonic_isBigTheta_log` and
  `CLRS.Chapter05.expectedHires_isBigTheta_log`.
- Chapter 16.1 now derives the sorted-order activity-selection exchange
  certificate and proves full finite-list maximum-cardinality optimality for
  `greedySelect`:
  `CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate` and
  `CLRS.ActivitySelection.greedySelect_maxCardinality`.
- Chapter 4.1 now proves the CLRS maximum-subarray crossing-helper layer:
  `CLRS.Chapter04.mem_crossingSubarrays_iff` and
  `CLRS.Chapter04.maxCrossingSubarray_correct`; the helper result is also
  connected back to the ordinary subarray spec by
  `CLRS.Chapter04.maxCrossingSubarray_isNonemptySubarray_append`.
- Chapter 4.1 also proves the split-combine proof interface needed by the
  recursive maximum-subarray algorithm:
  `CLRS.Chapter04.subarray_append_left_or_right_or_crossing` and
  `CLRS.Chapter04.subarray_append_optimal_of_cases`.
- Chapter 4.1 now also proves the executable combine step itself:
  `CLRS.Chapter04.maxSubarrayDivideStep_correct`.
- Chapter 4.1 now proves recursive divide-and-conquer correctness as well:
  `CLRS.Chapter04.maxSubarrayDivideTree_correct` for explicit split trees and
  `CLRS.Chapter04.maxSubarrayDivideFuel_correct` for a fuelled midpoint splitter.

## Next Proof Priorities

1. Chapter 23.2: add the sorted-prefix invariant needed to turn Kruskal's edge
   order into lightness certificates.
2. Chapter 4.1: add the runtime recurrence for the fuelled midpoint
   divide-and-conquer maximum-subarray selector.
3. Chapter 13.1: mechanize executable `RB-INSERT-FIXUP` on top of the local
   rotation/repaint repair certificates.

## Audit Rule

Do not move a section from `partial` to `proved` unless the corresponding
textbook-level theorem is both stated and proved in imported Lean source without
external certificates that encode the missing algorithmic step.
