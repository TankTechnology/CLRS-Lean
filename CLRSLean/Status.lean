/-!
# Proof Status

This page is the public status ledger for the web site.  It mirrors the longer
maintainer notes in `docs/proof-map.md`, but is written for readers who are
navigating the deployed pages.

## Status Labels

* `proved`: the named section theorem is proved in Lean for the current
  specification.
* `expository`: a reader-facing guide page with no theorem target.
* `partial`: important theorem infrastructure exists, but the full textbook
  claim is not complete.
* `statement`: the intended theorem interface exists, but proof work has not
  started.
* `blocked-design`: progress depends on choosing a stable representation.
* `blocked-mathlib`: progress depends on missing or inconvenient Mathlib
  infrastructure.
* `deferred-implementation`: the mathematical proof is in scope, but a
  low-level implementation proof is postponed.
* `future-work`: exercises, chapter-end problems, or strengthening passes
  outside the current main track.

## Proved

* 4.1 Maximum-subarray specification:
  {lit}`CLRS.Chapter04.mem_nonemptySubarrays_iff`,
  {lit}`CLRS.Chapter04.bestCandidate_correct`,
  {lit}`CLRS.Chapter04.maxSubarray_exists_of_ne_nil`,
  {lit}`CLRS.Chapter04.maxSubarray_correct`.
* 3.1 Asymptotic notation:
  `CLRS.Chapter03.isBigO_iff`,
  `CLRS.Chapter03.isLittleO_iff`,
  `CLRS.Chapter03.isBigOmega_iff`,
  `CLRS.Chapter03.isLittleOmega_iff`,
  `CLRS.Chapter03.isBigTheta_trans`.
* 4.5 Master method, exact-power model:
  {lit}`CLRS.Chapter04.h_formula`,
  {lit}`CLRS.Chapter04.master_case1_geometric`,
  {lit}`CLRS.Chapter04.master_case2_constant_forcing`,
  {lit}`CLRS.Chapter04.master_case3_tail_dominated`.
* 4.3 Substitution method, one-step recurrence model:
  {lit}`CLRS.Chapter04.substitution_upper_bound`,
  {lit}`CLRS.Chapter04.substitution_lower_bound`,
  {lit}`CLRS.Chapter04.substitution_sandwich`,
  {lit}`CLRS.Chapter04.linear_substitution_upper_bound`,
  {lit}`CLRS.Chapter04.geometric_substitution_upper_bound`.
* 4.4 Recursion-tree method, additive level-cost model:
  {lit}`CLRS.Chapter04.recursion_tree_additive_unroll`,
  {lit}`CLRS.Chapter04.recursion_tree_additive_upper_envelope`,
  {lit}`CLRS.Chapter04.recursion_tree_additive_lower_envelope`,
  {lit}`CLRS.Chapter04.recursion_tree_constant_level_cost`.
* 5.1 Hiring problem, finite rank-symmetry model:
  {lit}`CLRS.Chapter05.uniformAverage_indicator_singleton`,
  {lit}`CLRS.Chapter05.hireProbability_eq`,
  {lit}`CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`,
  {lit}`CLRS.Chapter05.expectedHires_eq_harmonic`.
* 2.1 Insertion sort:
  `CLRS.Chapter02.insertionSort_sorted`,
  `CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms:
  `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms:
  `CLRS.Chapter02.mergeSort_sortedLE`,
  `CLRS.Chapter02.mergeSort_perm`,
  `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`.
* 16.3 Huffman codes:
  `CLRS.HuffmanV2.optimum_huffman_freqs`.
* 10.1 Stacks and queues:
  `CLRS.Chapter10.pop_push`,
  `CLRS.Chapter10.dequeue_enqueue_empty`,
  `CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists:
  `CLRS.Chapter10.listSearch_sound`,
  `CLRS.Chapter10.mem_listInsert_self`,
  `CLRS.Chapter10.mem_listDeleteAll_iff`.
* 11.1 Direct-address tables:
  `CLRS.Chapter11.search_insert_same`,
  `CLRS.Chapter11.search_insert_other`,
  `CLRS.Chapter11.search_delete_same`,
  `CLRS.Chapter11.search_delete_other`.

## Partial

* 3.2 Standard functions:
  current results {lit}`CLRS.Chapter03.isLittleO_pow_pow`,
  {lit}`CLRS.Chapter03.isBigO_pow_pow`,
  {lit}`CLRS.Chapter03.isLittleO_pow_const_exp`,
  {lit}`CLRS.Chapter03.isLittleO_log_rpow`,
  {lit}`CLRS.Chapter03.isLittleO_exp_exp_of_lt`,
  {lit}`CLRS.Chapter03.isEquivalent_harmonic_log`,
  {lit}`CLRS.Chapter03.isBigTheta_harmonic_log`,
  {lit}`CLRS.Chapter03.isBigTheta_nat_floor_coerce`,
  {lit}`CLRS.Chapter03.isBigTheta_nat_ceil_coerce`,
  {lit}`CLRS.Chapter03.factorial_upper_bound`, and
  {lit}`CLRS.Chapter03.isLittleO_exp_vs_factorial`;
  remaining gap: add the full CLRS table of standard growth comparisons,
  including half-scale floor/ceiling facts and lower factorial bounds.
* 11.2 Chained hash tables:
  current results {lit}`CLRS.Chapter11.hashSearch_hashInsert_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashInsert_iff`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_self`, and
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_iff`;
  remaining gap: expected search time under simple uniform hashing needs a
  probability model over keys or hash functions.
* 12.1 Binary search trees:
  current results {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_inTree`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.maximum?_inTree`,
  {lit}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.successor?_least_greater`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`,
  {lit}`CLRS.Chapter12.BSTree.inTree_delete_iff`, and
  {lit}`CLRS.Chapter12.BSTree.delete_ordered`;
  remaining gap: parent-pointer successor/predecessor procedures, transplant,
  and pointer-level mutation remain future section targets.
* 13.1 Red-black trees:
  current results {lit}`CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_rotateRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`,
  {lit}`CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_repaintRoot`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`, and
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_black`;
  remaining gap: full RB insertion/deletion fixup algorithms are not yet
  mechanized.
* 16.1 Activity selection:
  current results {lit}`CLRS.ActivitySelection.earliest_finish_minFinish`,
  {lit}`CLRS.ActivitySelection.finishSorted_head_minFinish`,
  {lit}`CLRS.ActivitySelection.greedySelect_sublist`,
  {lit}`CLRS.ActivitySelection.greedySelect_feasible`, and
  {lit}`CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`;
  remaining gap: derive the exchange certificate automatically and prove
  maximum-cardinality optimality for the full recursive
  {lit}`CLRS.ActivitySelection.greedySelect` theorem.
* 23.1 Growing a minimum spanning tree:
  current result `CLRS.MST.safe_edge_of_lightest_crossing`;
  remaining gap: construct the concrete exchange edge from finite graph paths
  or cycles.
* 23.2 Kruskal and Prim:
  current result `CLRS.MST.kruskal_optimal`;
  remaining gap: derive lightness from sorted order and prove the final selected
  set is a spanning tree.

## Deferred or Blocked

* Union-find correctness: `deferred-implementation`.
  Reason: not needed for the mathematical MST proof.
* Concrete MST exchange edge: `blocked-design`.
  Reason: needs a stable finite path or walk representation.
* Full RAM semantics: `future-work`.
  Reason: requires a separate imperative machine and cost model.
* Chapter 4 Strassen and full Master Theorem extension:
  `future-work`.
  Reason: these sections are formalizable but still need their own models:
  block matrices and all-input floor/ceiling recurrence sandwiching.
* Chapter 4 maximum-subarray divide-and-conquer refinement: `future-work`.
  Reason: the exhaustive-search specification and optimality theorem are
  proved; the CLRS pseudocode and runtime proof remain to be connected to that
  specification.
* Chapter 4 extension from exact powers to all input sizes: `future-work`.
  Reason: needs a monotone recurrence model and floor/ceiling sandwiching.
* Chapter 5 logarithmic expected-hires asymptotics: `future-work`.
  Reason: Chapter 3.2 now proves the harmonic-number growth fact; Chapter 5
  still needs a section-level theorem connecting the expected-hiring result to
  that asymptotic wrapper.
* General merge-sort recurrence: `future-work`.
  Reason: needs floor and ceiling arithmetic for all input sizes.
* CLRS exercises and chapter-end problems: `future-work`.
  Reason: kept separate from the first main-theorem pass.

## Reader Contract

The status table is intentionally conservative.  A section is not marked
`proved` merely because the algorithm idea is clear; it needs a named Lean
theorem that compiles for the stated model.  A section marked `partial` should
say exactly which mathematical or representation layer remains.
-/
