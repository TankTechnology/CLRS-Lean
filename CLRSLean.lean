import CLRSLean.Chapter_01
import CLRSLean.Chapter_02
import CLRSLean.Chapter_03
import CLRSLean.Chapter_04
import CLRSLean.Chapter_05
import CLRSLean.Chapter_10
import CLRSLean.Chapter_11
import CLRSLean.Chapter_12
import CLRSLean.Chapter_13
import CLRSLean.Chapter_16
import CLRSLean.Chapter_23
import CLRSLean.Status
import CLRSLean.Workflow

/-!
# CLRS-Lean

CLRS-Lean is a Lean 4 companion to CLRS-style algorithm proofs.  The project is
organized as a readable online book: each chapter has a short guide page, and
each selected textbook section has a literate Lean page containing the formal
model, the public theorem interface, and the proof.

## Project Aim

The goal is not to mechanically translate pseudocode line by line.  The first
target is the mathematical proof content of the textbook: loop invariants,
exchange arguments, cut properties, recurrences, and optimal-substructure
claims.  Low-level implementation proofs, such as union-find or heap
correctness, are added only when they are needed for the main theorem.

This keeps the site useful for three kinds of readers:

* algorithm readers who want the proof idea before reading Lean code;
* Lean readers who want stable theorem names and proof patterns;
* contributors who need an honest map of what is proved, partial, or deferred.

## Reading Route

Start with the chapter pages in the sidebar.

* Chapter 1 - Algorithms: the project reading contract and the way CLRS-Lean
  turns textbook claims into Lean definitions plus theorems.
* Chapter 2 - Getting Started: sorting correctness, a lightweight runtime bound,
  and a merge-sort recurrence.
* Chapter 3 - Growth of Functions: CLRS-style wrappers around Mathlib
  asymptotics plus selected standard growth facts.
* Chapter 4 - Divide-and-Conquer: maximum-subarray specification correctness,
  recurrence proof infrastructure for the substitution and recursion-tree
  methods, plus the proved exact-power Master method core; Strassen remains a
  planned algorithm track.
* Chapter 5 - Probabilistic Analysis: the finite rank-symmetry proof for the
  hiring problem.
* Chapter 10 - Elementary Data Structures: functional stack, queue, and
  linked-list operation proofs.
* Chapter 11 - Hash Tables: direct-address table correctness and deterministic
  chained-hash-table lookup facts.
* Chapter 12 - Binary Search Trees: search, minimum/maximum, insertion,
  functional successor/predecessor, and functional deletion correctness for an
  inductive BST model.
* Chapter 13 - Red-Black Trees: local rotation, recoloring, and red-black shape
  invariant lemmas.
* Chapter 16 - Greedy Algorithms: activity-selection exchange infrastructure
  and the complete Huffman optimality proof, currently the flagship greedy case
  study.
* Chapter 23 - Minimum Spanning Trees: the MST cut property and the
  mathematical Kruskal skeleton.
* Proof Status: a compact ledger of proved, partial, blocked, and deferred work.
* Workflow: the contribution loop for adding or strengthening a CLRS section.

## Current Coverage

* Chapter 1: `expository`.
  No theorem target; this page explains the project conventions.
* 2.1 Insertion sort: `proved`.
  Public results: `CLRS.Chapter02.insertionSort_sorted`,
  `CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms: `proved`.
  Public result: `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms: `proved`.
  Public results: `CLRS.Chapter02.mergeSort_sortedLE`,
  `CLRS.Chapter02.mergeSort_perm`,
  `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`.
* 3.1 Asymptotic notation: `proved`.
  Public results: `CLRS.Chapter03.isBigO_iff`,
  `CLRS.Chapter03.isLittleO_iff`,
  `CLRS.Chapter03.isBigTheta_trans`.
* 3.2 Standard functions: `partial`.
  Current results: `CLRS.Chapter03.isLittleO_pow_pow`,
  `CLRS.Chapter03.factorial_upper_bound`,
  `CLRS.Chapter03.isLittleO_exp_vs_factorial`.
* 4.1 Maximum subarray: `proved` for the exhaustive-search specification.
  Public results: `CLRS.Chapter04.mem_nonemptySubarrays_iff`,
  `CLRS.Chapter04.bestCandidate_correct`,
  `CLRS.Chapter04.maxSubarray_exists_of_ne_nil`,
  `CLRS.Chapter04.maxSubarray_correct`.
* 4.2 Strassen's algorithm: `future-work`.
  Planned target: block-matrix reconstruction correctness.
* 4.3 Substitution method: `proved` for one-step recurrence bounds.
  Public results: `CLRS.Chapter04.substitution_upper_bound`,
  `CLRS.Chapter04.substitution_lower_bound`,
  `CLRS.Chapter04.linear_substitution_upper_bound`,
  `CLRS.Chapter04.geometric_substitution_upper_bound`.
* 4.4 Recursion-tree method: `proved` for additive level-cost expansions.
  Public results: `CLRS.Chapter04.recursion_tree_additive_unroll`,
  `CLRS.Chapter04.recursion_tree_additive_upper_envelope`,
  `CLRS.Chapter04.recursion_tree_constant_level_cost`.
* 4.5 Master method: `proved` for exact-power recurrences.
  Public results: `CLRS.Chapter04.master_case1_geometric`,
  `CLRS.Chapter04.master_case2_constant_forcing`,
  `CLRS.Chapter04.master_case3_tail_dominated`.
* 4.6 Proof of the master theorem: `future-work`.
  Planned target: extend the exact-power proof to all natural input sizes with
  floor/ceiling sandwiching.
* 5.1 Hiring problem: `proved` for the finite rank-symmetry model.
  Public results: `CLRS.Chapter05.hireProbability_eq`,
  `CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`.
* 10.1 Stacks and queues: `proved` for the functional-list model.
  Public results: `CLRS.Chapter10.pop_push`,
  `CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists: `proved` for the functional-list model.
  Public results: `CLRS.Chapter10.listSearch_sound`,
  `CLRS.Chapter10.mem_listDeleteAll_iff`.
* 11.1 Direct-address tables: `proved` for the functional table model.
  Public results: `CLRS.Chapter11.search_insert_same`,
  `CLRS.Chapter11.search_delete_same`.
* 11.2 Chained hash tables: `partial`.
  Current results: `CLRS.Chapter11.hashSearch_hashInsert_self`,
  `CLRS.Chapter11.hashSearch_hashInsert_iff`.
* 12.1 Binary search trees: `partial`.
  Current results: `CLRS.Chapter12.BSTree.search_eq_true_iff`,
  `CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  `CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  `CLRS.Chapter12.BSTree.successor?_least_greater`,
  `CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  `CLRS.Chapter12.BSTree.inTree_insert_iff`,
  `CLRS.Chapter12.BSTree.insert_ordered`,
  `CLRS.Chapter12.BSTree.inTree_delete_iff`,
  `CLRS.Chapter12.BSTree.delete_ordered`.
* 13.1 Red-black trees: `partial`.
  Current results: `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  `CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`,
  `CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  `CLRS.Chapter13.RBTree.redBlackShape_repaint_black`.
* 16.1 Activity selection: `partial`.
  Current results: `CLRS.ActivitySelection.earliest_finish_minFinish`,
  `CLRS.ActivitySelection.finishSorted_head_minFinish`,
  `CLRS.ActivitySelection.greedySelect_sublist`,
  `CLRS.ActivitySelection.greedySelect_feasible`,
  `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`.
* 16.3 Huffman codes: `proved`.
  Public result: `CLRS.HuffmanV2.optimum_huffman_freqs`.
* 23.1 Growing a minimum spanning tree: `partial`.
  Current result: `CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: `partial`.
  Current result: `CLRS.MST.kruskal_optimal`.

## Status Policy

The site uses explicit status labels instead of hiding incomplete work.

* `proved`: the named theorem is proved in Lean without relying on `sorry`.
* `expository`: the page is a reader guide rather than a theorem-bearing
  section.
* `partial`: important theorem infrastructure exists, but the full textbook
  section is not yet complete.
* `blocked-design`: progress needs a representation decision, such as paths,
  walks, heaps, arrays, or cost semantics.
* `deferred-implementation`: a low-level implementation proof is useful but not
  required for the current mathematical theorem.
* `future-work`: valuable extensions, exercises, or chapter-end problems.

## Build and Deployment

The deployed site is generated from the Lean source by Verso:

```
lake build
lake build :literateHtml
```

GitHub Actions runs the same pipeline and publishes the generated `_site`
directory to GitHub Pages.

Repository: [TankTechnology/CLRS-Lean](https://github.com/TankTechnology/CLRS-Lean)
-/
