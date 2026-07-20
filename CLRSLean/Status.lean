/-!
# Proof Status

This page gives a concise reader-facing interpretation of CLRS-Lean's current
proof state.  The generated **Progress Dashboard** owns chapter counts and
status rows; section modules own formal truth; {lit}`docs/proof-map.md` records
the detailed maintainer ledger.

## Status Labels

* {lit}`main-proof-complete`: the advertised main theorem stack is complete for
  the current model.
* {lit}`main-proof-complete-for-correctness`: algorithm correctness is complete;
  explicit work, RAM, or imperative refinement remains.
* {lit}`selected-section-complete`: represented sections are complete without a
  claim about the unrepresented remainder of the chapter.
* {lit}`partial`: meaningful theorem infrastructure exists, but a central
  textbook theorem or refinement remains.
* {lit}`not-started`: no represented section exists on {lit}`main`.
* {lit}`expository`: a guide page with no theorem target.

## Complete For The Advertised Scope

* **Chapter 2:** insertion sort, merge sort, and the represented cost/recurrence
  wrappers.
* **Chapter 3:** asymptotic wrappers, the standard-function comparison table,
  Fibonacci growth, and the iterated logarithm.
* **Chapter 4:** maximum-subarray correctness, the costed executable midpoint
  selector with execution-attached scan counts and an all-input
  {lit}`Theta(n log n)` bound, recursive Strassen correctness/runtime, and
  the textbook-facing Master cases are proved.  Explicit split-tree
  construction, integer operations, {lit}`List` allocation/copying, and RAM
  semantics remain optional lower-level refinements.
* **Chapter 6:** the current heap predicate, recursive {lit}`MAX-HEAPIFY`,
  bottom-up {lit}`BUILD-MAX-HEAP`, heapsort, and represented priority-queue
  operation specifications.  A costed execution mirrors heapify, build-heap,
  and heapsort, erases to those algorithms, and proves coarse connected
  {lit}`O(n)`, {lit}`O(n²)`, and {lit}`O(n²)` unit control-step envelopes.
  This metric counts visited heapify frames and nontrivial extraction
  transitions, but not build-loop orchestration, guards, list-operation costs,
  or RAM semantics; tight textbook bounds remain refinements.
* **Chapter 8 correctness:** represented counting-sort, radix-sort, and
  bucket-sort correctness.  The CLRS unit-cost bucket-sort random variable is
  {lit}`CLRS.Chapter08.textbookBucketSortCost`; its expectation identity is
  {lit}`CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`,
  and {lit}`CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO` proves linear
  expectation.  The remaining bucket-sort layer is a single-pass executable
  bucket builder, a costed per-bucket sorter, and a refinement theorem
  connecting their execution cost to the abstract model.
* **Chapter 9:** pairwise simultaneous extrema, order-statistic correctness,
  a schedule-driven RANDOMIZED-SELECT path cost with erasure/rank correctness,
  the nested fresh-choice expectation and its bridge to the CLRS larger-side
  majorizer ({lit}`≤ 4 * c * n`), and end-to-end recursive median-of-medians
  worst-case comparisons.  The randomized metric charges
  {lit}`c * currentLength` partition work only; concrete RNG, internal
  {lit}`selectByRank?` sorting cost, list primitives, and RAM accounting remain
  lower-level refinements.
* **Chapter 21:** abstract and executable disjoint-set correctness, weighted
  linked-list analysis, reachable rank mass, concrete Batteries traversal
  costs, and the {lit}`O((m+n) alpha(n))` potential analysis.
* **Chapter 22 correctness:** BFS shortest distances and predecessor tree, DFS
  white-path/timestamp/ancestor/edge-classification theory, Kahn and DFS
  topological sorting, and Kosaraju SCC partition correctness.
* **Chapter 23 correctness and functional implementation:** canonical exchange,
  stateful Kruskal, executable indexed-queue Prim, and their algorithm-level
  work bounds.
* **Chapter 11 correctness:** deterministic tables, SUHA true-expectation
  search costs, universal hashing, open addressing, and perfect hashing.
* **Chapter 12 correctness:** functional BSTs, zipper navigation/transplant,
  and the represented pointer-heap transplant/insert refinement.
* **Chapter 13 correctness:** executable red-black insertion and deletion with
  exact membership correctness, red-black shape preservation through both
  operations ({lit}`redBlackShape_insert`, {lit}`redBlackShape_delete` via the
  {lit}`baldL`/{lit}`baldR`/{lit}`splitMin`/{lit}`join` doubly-black
  rebalancing pipeline), and the logarithmic-height theorem (CLRS Lemma 13.1).
* **Chapter 15 represented sections:** rod cutting, matrix chain, LCS, and
  optimal BST optimality with executable recurrence/reconstruction layers.
* **Chapter 16:** activity selection, the greedy meta-theorem, Huffman coding,
  matroid greedy, and task scheduling.
* **Chapter 17 represented sections:** aggregate, accounting, and potential
  methods plus stack/counter and dynamic-table amortized analyses.
* **Chapter 20 correctness:** all seven operations of the recursive cached-
  extrema vEB model and their control-flow-aware {lit}`O(log log u)` bounds.
* **Selected complete sections:** Chapter 5.1--5.4 core models and Chapter
  10.1, 10.2, and 10.4 functional structures.  Chapter 5 also represents the
  longest-streak tail bound and an executable on-line hiring strategy; their
  remaining asymptotics are chapter-end Problems.  Pointer/RAM refinements are
  separate tracks.

## Structured But Partial

* **Chapter 7:** functional and mutable-array correctness, comparison
  recurrences, random-permutation symmetry, and pairwise comparison probability
  are proved.  The total-comparison random variable and expectation-sum bridge
  remain.
* **Chapter 14:** order-statistic augmentation (including the size invariant
  threaded through executable red-black insertion and deletion via
  {lit}`OSRBTree.wellSized_insert` and {lit}`OSRBTree.wellSized_delete`),
  generic local augmentation facts, and interval-search correctness exist.  The
  remaining core group is threading the generic Section 14.3 augmentation
  interface ({lit}`AugmentedRBTree`) through executable red-black deletion.
* **Chapters 18-19:** B-trees and Fibonacci heaps have substantial mathematical
  or size-level specifications.  B-tree structural invariants and the
  executable Fibonacci-heap forest operations/cost analysis remain central
  theorem groups.
* **Chapter 24:** Bellman-Ford, DAG SSSP, Dijkstra's greedy theorem, a concrete
  state/step/loop skeleton, and difference constraints are represented.  The
  loop still needs an initialization-to-invariant bridge and final distance-correctness
  theorem.
* **Chapter 25:** FASTER-APSP is correct; Floyd-Warshall currently has its
  recurrence/work wrapper; Johnson currently has reweighting algebra.  Their
  remaining correctness interfaces are tracked explicitly.
* **Chapter 26:** the flow model, generic no-augmenting-path maximality,
  Edmonds-Karp monotonic distance, and one MFMC direction are proved.  The MFMC
  converse, executable Edmonds-Karp complexity theorem, and Section 26.3 remain.

## Not Represented On Main

Chapters 27-35 do not currently have represented section modules on
{lit}`main`.  Chapters 24-26 are represented but remain partial as described
above.  Open pull requests are not counted until their scope is reviewed,
merged, and added to the progress source.

## Sealed Chapters 21-23 Boundary

Chapters 21--23 are complete for their advertised boundaries.  Their
closure boundaries are protected by focused interface and closure tests plus
dated audits under {lit}`docs/proof-audits/`.

The following are refinements and do not reopen the completed correctness
milestone:

* exact work counts and {lit}`O(V + E)` packaging;
* imperative adjacency-list or RAM refinement;
* mutable-array refinement of the Chapter 23 union-find and Prim queue models;
* exercises and chapter-end problems.

## Highest-Value Open Proof Groups

1. Close Chapter 24 by aligning Dijkstra initialization with its invariant and
   proving final loop distance correctness.
2. Prove Floyd-Warshall correctness, then Johnson's end-to-end correctness and
   the remaining path-reconstruction/negative-cycle interfaces in Chapter 25.
3. Complete the MFMC converse, Edmonds-Karp counting theorem, and bipartite-
   matching reduction in Chapter 26.
4. Thread the generic Chapter 14 augmentation interface
   ({lit}`AugmentedRBTree`) through executable red-black deletion, mirroring
   the Chapter 13 {lit}`del` pipeline.
5. Close Chapter 7's total-comparison expectation bridge.

## Reader Contract

A {lit}`proved` or complete label always refers to a named Lean theorem for an
explicit model.  It never silently means that every exercise, cost model, or
imperative implementation has been completed.  A {lit}`partial` label should
name the remaining mathematical or representation layer, and dated audits
should be treated as historical evidence rather than a live status source.
-/
