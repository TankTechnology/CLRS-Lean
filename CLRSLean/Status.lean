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
* **Chapter 7 represented sections:** functional and mutable-array quicksort
  correctness, comparison recurrences, random-permutation symmetry, pairwise
  comparison probability, the sum-of-probabilities bridge
  ({lit}`sum_compared_prob_eq_expectedComparisons`), and the
  {lit}`Theta(n log n)` expected-comparison bound.
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
* **Chapter 24 represented sections:** Bellman-Ford, DAG shortest paths,
  Dijkstra's greedy theorem, the proved initialization/loop invariant bridge
  and final {lit}`dijkstraLoop_correct` theorem, and difference constraints.
* **Chapter 25 correctness:** FASTER-APSP, Floyd-Warshall correctness,
  predecessor-path reconstruction with walk and weight guarantees,
  negative-cycle detection, transitive closure, and Johnson's end-to-end
  shortest-distance theorem.
* **Chapter 26:** concrete augmenting-path augmentation, the Max-Flow Min-Cut
  equivalence, executable residual BFS and Edmonds-Karp, the {lit}`O(VE²)`
  augmentation bound, and maximum bipartite matching through Theorem 26.12.
  Sections 26.4 and 26.5 are outside the current selected milestone.
* **Chapter 27:** the pure-functional main-text boundary is complete through
  Section 27.3.  It includes the total ready-set greedy scheduler and
  `Tₚ ≤ T₁/p + T∞`; exact logarithmic parallel-loop bounds; executable
  P-ADD/P-MATMUL correctness with execution-attached Θ(n²)/Θ(log n) and
  Θ(n³)/Θ(log² n) costs; and executable P-MERGE/P-MERGE-SORT correctness,
  recurrence links, universal upper bounds, and explicit matching worst-case
  span families.  The historical {lit}`Section_27_2_4_Algorithms` path remains
  for import compatibility, while parallel-Strassen recurrences live in a
  separately labeled extension.  Mutable arrays, RAM-level costs, exercises,
  and chapter-end problems are optional refinements outside this boundary.
* **Chapter 28:** Sections 28.1--28.3 are complete at the finite-matrix layer.
  The chapter includes LUP decomposition (Theorem 28.1), executable forward
  and backward substitution, LUP-SOLVE correctness, matrix inversion
  (Theorem 28.2), Cholesky decomposition with uniqueness (Theorem 28.3),
  least-squares approximation (Theorem 28.4), and the principal quadratic and
  cubic work bounds.  Executable LUP factorization directly from an input
  matrix and RAM-level cost semantics remain optional refinements.
* **Chapter 29:** Sections 29.1--29.5 are complete at the finite real-matrix
  and pure-functional tableau layer.  The chapter includes exact standard/slack
  equivalence; shortest-path, maximum-flow, minimum-cost-flow, and
  multicommodity-flow LPs; exact PIVOT semantics; terminating Bland SIMPLEX with
  anti-cycling and finite termination; weak and strong duality; complementary
  slackness; phase-I initialization; and a certified infeasible/optimal/
  unbounded solver.  Mutable tableau storage, floating-point analysis, RAM
  constants, exercises, and chapter-end problems are optional refinements.
* **Chapter 11 correctness:** deterministic tables, SUHA true-expectation
  search costs, universal hashing, open addressing, and perfect hashing.
* **Chapter 12 correctness:** functional BSTs, zipper navigation/transplant,
  and the represented pointer-heap transplant/insert refinement.
* **Chapter 13 correctness:** executable red-black insertion and deletion with
  exact membership correctness, red-black shape preservation through both
  operations ({lit}`redBlackShape_insert`, {lit}`redBlackShape_delete` via the
  {lit}`baldL`/{lit}`baldR`/{lit}`splitMin`/{lit}`join` doubly-black
  rebalancing pipeline), and the logarithmic-height theorem (CLRS Lemma 13.1).
* **Chapter 14 correctness:** order-statistic and interval-tree augmentation,
  including the size-specialized deletion refinement and the generic
  {lit}`AugmentedRBTree.wellAugmented_delete` invariant-preservation pipeline.
  The generic {lit}`toRB_delete` erasure/refinement lemma and pointer/RAM
  semantics remain separate refinements.
* **Chapter 15 represented sections:** rod cutting, matrix chain, LCS, and
  optimal BST optimality with executable recurrence/reconstruction layers.
* **Chapter 16:** activity selection, the greedy meta-theorem, Huffman coding,
  matroid greedy, and task scheduling.
* **Chapter 17 selected sections:** the represented aggregate, accounting, and
  potential methods plus stack/counter and dynamic-table amortized analyses are
  complete.  Allocator constants, lower-level RAM semantics, and broader
  interleaved-trace packaging are optional refinements.
* **Chapter 18 correctness:** separator-guided search, real top-level insertion
  with full-root splitting, exact executable deletion, and the structural
  minimum-key/logarithmic-height theorem.  The count theorem uses key slots and
  requires no uniqueness premise; the root theorem exposes the legal empty
  tree explicitly, while for {lit}`2 ≤ t` the logarithmic wrapper applies to
  every {lit}`WellFormed` tree.  No tree-shape equality with the flat
  specification operations is claimed.  Disk pages, pointer mutation, I/O
  counts, and RAM costs remain optional lower-level refinements.
* **Chapter 19 correctness and amortized analysis:** the persistent executable
  Fibonacci heap has a cached minimum, exact duplicate-preserving key bags,
  degree-bucket {lit}`LINK`/{lit}`CONSOLIDATE`, extract-min, occurrence paths
  and zippers, arbitrary-node CUT/CASCADING-CUT, decrease-key, and delete.
  These transitions preserve the global mark-aware validity invariant.  The
  {lit}`t(H) + 2m(H)` analysis proves constant amortized decrease-key,
  logarithmic extract-min/delete, and an exact trace-level telescope.  Mutable
  circular lists and RAM/pointer costs remain optional lower-level refinements.
* **Chapter 20 correctness:** all seven operations of the recursive cached-
  extrema vEB model and their control-flow-aware {lit}`O(log log u)` bounds.
* **Selected complete sections:** Chapter 5.1--5.4 core models; Chapter 10.1,
  10.2, and 10.4 functional structures; and Chapter 32.1 string matching.
  Chapter 5 also represents the
  longest-streak tail bound and an executable on-line hiring strategy; their
  remaining asymptotics are chapter-end Problems.  Pointer/RAM refinements and
  the unrepresented later sections of Chapter 32 are separate tracks.

## Structured But Partial

* **Chapter 33:** Section 33.1 represents point/vector and line-segment
  definitions, cross-product algebra, and the orientation specification.
  Correctness of {lit}`segmentIntersect` against an independent geometric
  intersection specification, including the shared-endpoint cases, remains.

## Not Represented On Main

Chapters 30--31 and 34--35 do not currently have represented section modules
on {lit}`main`.  Chapter 33.1 is represented but partial; Chapter 32.1 is
complete for its selected-section scope.  Open pull requests
are not counted until their scope is reviewed, merged, and added to the
progress source.

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

## Reader Contract

A {lit}`proved` or complete label always refers to a named Lean theorem for an
explicit model.  It never silently means that every exercise, cost model, or
imperative implementation has been completed.  A {lit}`partial` label should
name the remaining mathematical or representation layer, and dated audits
should be treated as historical evidence rather than a live status source.
-/
