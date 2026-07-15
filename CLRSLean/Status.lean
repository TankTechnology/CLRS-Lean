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
  fresh-choice RANDOMIZED-SELECT expected comparisons, and end-to-end
  recursive median-of-medians worst-case comparisons.
* **Chapter 21:** abstract and executable disjoint-set correctness, weighted
  linked-list analysis, reachable rank mass, concrete Batteries traversal
  costs, and the {lit}`O((m+n) alpha(n))` potential analysis.
* **Chapter 22 correctness:** BFS shortest distances and predecessor tree, DFS
  white-path/timestamp/ancestor/edge-classification theory, Kahn and DFS
  topological sorting, and Kosaraju SCC partition correctness.
* **Selected complete sections:** Chapter 5.1 hiring, Chapter 10.1-10.2
  functional elementary structures, and Chapter 16.1/16.3 activity selection
  and Huffman coding.

## Structured But Partial

* **Chapters 3-4:** the asymptotic wrapper, broad standard-function library,
  exact-power and all-input Master-theorem stack, and textbook-facing case 1,
  case 2, and regular case 3 comparison scales are proved.  The remaining work
  is table completion and algorithm/runtime refinement, not the core Master
  case-3 bridge.
* **Chapter 5:** Sections 5.1--5.3 and the birthday/balls-and-bins part of
  Section 5.4 are proved.  Section 5.4 also has the longest-streak tail bound
  and an executable on-line threshold hiring strategy with exact selection
  contracts and a finite success-probability definition.  The expected-longest-
  streak logarithmic theorem, the hiring success-probability harmonic formula,
  and its {lit}`1/e` asymptotic remain open.
* **Chapters 7 and 11:** deterministic correctness and recurrence or finite-
  average layers exist.  End-to-end randomized expected-time or hashing-model
  bridges remain central gaps.
* **Chapters 12-14:** functional BST operations plus a zipper-based
  parent-navigation/transplant layer, executable red-black insertion,
  order-statistic augmentation, generic local augmentation facts, and interval-
  search correctness exist.  Imperative pointer mutation, red-black
  deletion/height, and integration between balancing and augmentation remain.
* **Chapter 15:** rod cutting, matrix-chain multiplication, LCS, and optimal BST
  have mathematical optimality layers and pure executable recurrence or
  reconstruction results.  Rod cutting additionally has a mutable-array bottom-up
  table proved to refine the pure recurrence value.  Mutable-array/memoized
  refinement for the remaining DP sections and explicit RAM costs remain.
* **Chapters 17-19:** amortized analysis, B-trees, and Fibonacci heaps have
  substantial mathematical or size-level specifications.  Pointer/page
  representations and sharper implementation theorems remain.
* **Chapter 20:** the recursive cached-min/max van Emde Boas model proves all
  seven operations correct, with constant cached extrema and control-flow-aware
  `O(log log u)` bounds for the recursive operations.  Concrete pointer/array
  allocation and hardware-level RAM timing remain a separate implementation
  refinement.
* **Chapter 23:** mathematical MST correctness is sealed.  Canonical tree
  paths generate exchange edges automatically, sorted exact-component Kruskal
  has an end-to-end optimum wrapper, and complete Prim light-edge traces return
  minimum spanning trees.  Stateful scans, priority queues, and RAM costs are
  implementation refinements.

## Not Represented On Main

Chapters 24-35 do not currently have represented section modules on
{lit}`main`.  Open pull requests are not counted until their scope is reviewed,
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

1. Build the reusable finite probability/expectation layer and close one
   randomized theorem end-to-end, starting with Chapter 7 comparison
   probability and total expectation.
2. Prove red-black deletion/fixup and the logarithmic-height theorem, then
   connect balancing to Chapter 14 augmentation.
3. Open Chapter 24 with a weighted graph model and Bellman-Ford correctness.
4. Add the concrete cost or imperative refinements that connect existing
   mathematical theorem interfaces to CLRS pseudocode.

## Reader Contract

A {lit}`proved` or complete label always refers to a named Lean theorem for an
explicit model.  It never silently means that every exercise, cost model, or
imperative implementation has been completed.  A {lit}`partial` label should
name the remaining mathematical or representation layer, and dated audits
should be treated as historical evidence rather than a live status source.
-/
