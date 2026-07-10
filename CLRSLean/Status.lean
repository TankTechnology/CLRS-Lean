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
  operation specifications.
* **Chapter 8 correctness:** represented counting-sort, radix-sort, and
  bucket-sort correctness.  Imperative output-array and full probabilistic cost
  semantics remain refinements.
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
* **Chapters 7, 9, and 11:** deterministic correctness and recurrence or finite-
  average layers exist.  A reusable finite probability/expectation model and
  end-to-end randomized expected-time bridges remain central gaps.
* **Chapters 12-14:** functional BST operations, executable red-black insertion,
  order-statistic augmentation, generic local augmentation facts, and interval-
  search correctness exist.  Pointer refinement, red-black deletion/height,
  and integration between balancing and augmentation remain.
* **Chapter 15:** rod cutting, matrix-chain multiplication, LCS, and optimal BST
  have mathematical optimality layers and pure executable recurrence or
  reconstruction results.  Mutable-array/memoized refinement and explicit RAM
  costs remain.
* **Chapters 17-20:** amortized analysis, B-trees, Fibonacci heaps, and van Emde
  Boas trees have substantial mathematical or size-level specifications.
  Pointer/page/cluster representations and sharper asymptotic implementation
  theorems remain.
* **Chapter 21:** abstract partition semantics, weighted linked-list
  correctness and rewrite bounds, executable Batteries union-find correctness,
  rank/path bounds, and the Chapter 23 cycle-test bridge are proved.  A concrete
  step-counting instantiation of the inverse-Ackermann potential certificate
  remains.
* **Chapter 23:** cut-property, exchange-certificate, and Kruskal theorem layers
  exist, now with an extensional union-find cycle-test refinement.  Automatic
  exchange-path extraction, a stateful scan, a fully local recursive wrapper,
  and Prim remain.

## Not Represented On Main

Chapters 24-35 do not currently have represented section modules on
{lit}`main`.  Open pull requests are not counted until their scope is reviewed,
merged, and added to the progress source.

## Sealed Chapter 22 Boundary

Chapter 22 is {lit}`main-proof-complete-for-correctness`.  The closure boundary
is protected by {lit}`Tests/Chapter_22_Interface.lean`,
{lit}`Tests/Chapter_22_Closure.lean`, and the dated closure audit under
{lit}`docs/proof-audits/`.

The following are refinements and do not reopen the completed correctness
milestone:

* exact work counts and {lit}`O(V + E)` packaging;
* imperative adjacency-list or RAM refinement;
* exercises and chapter-end problems.

## Highest-Value Open Proof Groups

1. Build the reusable finite probability/expectation layer and close one
   randomized theorem end-to-end, starting with Chapter 7 comparison
   probability and total expectation.
2. Complete Chapter 23's automatic exchange extraction and Prim interface;
   refine the new union-find bridge to a stateful costed Kruskal scan.
3. Prove red-black deletion/fixup and the logarithmic-height theorem, then
   connect balancing to Chapter 14 augmentation.
4. Add the concrete cost or imperative refinements that connect existing
   mathematical theorem interfaces to CLRS pseudocode.

## Reader Contract

A {lit}`proved` or complete label always refers to a named Lean theorem for an
explicit model.  It never silently means that every exercise, cost model, or
imperative implementation has been completed.  A {lit}`partial` label should
name the remaining mathematical or representation layer, and dated audits
should be treated as historical evidence rather than a live status source.
-/
