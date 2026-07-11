# Proof Status Board

This board is the compact planning view for CLRS-Lean.  Chapter counts and
status labels come from [`clrs-proof-progress.csv`](clrs-proof-progress.csv).
The detailed theorem ledger is [`proof-map.md`](proof-map.md).  This page owns
priorities, not theorem-by-theorem duplication.

Last repository-wide status reconciliation: 2026-07-11.

## Complete For The Current Scope

| Scope | Completed boundary | Refinements that do not reopen it |
| --- | --- | --- |
| Chapter 2 | Insertion sort, merge sort, and represented cost/recurrence results | Full RAM semantics and arbitrary-size merge-sort recurrence |
| Chapter 5.1 | Hiring probability, harmonic expectation, and logarithmic asymptotic bound | General probability toolkit and other randomized examples |
| Chapter 6 | Heap predicate, heapify, build-heap, heapsort, and represented priority-queue correctness | Line-by-line RAM costs |
| Chapter 8 correctness | Represented counting-sort, radix-sort, and bucket-sort correctness | Mutable output array and full independent-input cost model |
| Chapter 10.1-10.2 | Functional stacks, queues, and linked lists | Pointer memory and allocation |
| Chapter 16.1 and 16.3 | Activity-selection and Huffman optimality | Other greedy sections |
| Chapter 21 | Partition semantics, weighted linked-list analysis, executable Batteries union-find, reachable rank mass, and `O((m+n) alpha(n))` amortization | Lower-level RAM constants and stateful Chapter 23 integration |
| Chapter 22 correctness | BFS shortest paths/predecessor tree, DFS theory, Kahn and DFS topological sorts, Kosaraju SCC partition | Work counts, `O(V + E)`, and imperative/RAM refinement |
| Chapter 23 correctness and functional implementation | Cut property, unique tree paths, automatic exchange, sorted and stateful Kruskal, concrete indexed-queue Prim, and explicit algorithm-level work bounds | `Batteries.BinaryHeap` array refinement and mutable/RAM write accounting |

Chapters 21-23 are formally sealed by their interface tests and dated
closure audits.  Their listed implementation refinements are new layers, not
missing core theorem groups.

## Structured But Partial

| Chapter | Strongest current layer | Central remaining group |
| --- | --- | --- |
| 3 | CLRS asymptotic wrappers and broad standard-function facts | Complete the standard-function comparison table |
| 4 | Maximum subarray, Strassen 2x2, substitution, recursion trees, and textbook-facing Master cases 1-3 | Recursive Strassen and algorithm/RAM refinements |
| 7 | Functional quicksort correctness, comparison recurrence, harmonic bounds | Explicit random-permutation/pivot probability model and end-to-end expectation |
| 9 | Rank selection and executable median-of-medians correctness with linear recurrence wrapper | Randomized SELECT and concrete executable cost semantics |
| 11 | Deterministic hash tables and finite-uniform bucket averages | Random key/hash-function model with independence |
| 12 | Functional BST operations plus zipper-based parent navigation, transplant, and deletion equivalence | Imperative in-place pointer mutation and RAM refinement |
| 13 | Executable red-black insertion, invariant proofs, and the logarithmic-height theorem (Lemma 13.1) | Deletion/fixup (`RB-DELETE`/`RB-DELETE-FIXUP`) |
| 14 | Order-statistic augmentation, generic local augmentation, and interval-search correctness | Integration with red-black balancing and a final general augmentation interface |
| 15 | Rod cutting, matrix chain, LCS, and optimal BST optimality with pure executable tables/reconstruction | Mutable-array/memoized refinement and RAM costs |
| 17 | Aggregate/accounting/potential framework and represented examples | Mutable arrays, allocator costs, sharper table model |
| 18 | Mathematical B-tree search/split/insert/delete specs | Occupancy/depth invariants and page mutation |
| 19 | Abstract finite-set Fibonacci-heap operation specs and potential facts | Pointer forest, cascading cuts, consolidation, true degree theorem |
| 20 | vEB arithmetic and finite-set operation specs | Recursive cluster representation and `O(log log u)` bridge |

## Not Represented On Main

- Chapters 24-35.

Open branches and pull requests are intentionally excluded until they are
reviewed, merged, registered in `literate.toml`, and added to the progress CSV.

## Next Proof Plan

| Priority | Target | Concrete deliverable |
| --- | --- | --- |
| 0 | Chapters 5/7/8/9/11 probability infrastructure | General finite `Fintype` expectation/probability API, then Chapter 7 total comparison expectation and `O/Theta(n log n)` bridge |
| 1 | Chapter 13/14 tree integration | Red-black deletion/height, then augmentation preservation through balancing |
| 2 | Chapter 24 shortest-path opening | Establish the weighted directed-graph model and Bellman-Ford correctness boundary |
| 3 | Chapter 23 implementation track | Add a stateful costed Kruskal scan using Chapter 21's proved inverse-Ackermann machine bound |
| 4 | Existing partial implementation layers | Select one concrete pointer, mutable-array, or RAM refinement and finish it end-to-end |

## High-Difficulty Queue

| Scope | Why it is difficult | Recommended boundary |
| --- | --- | --- |
| Randomized expected-time analysis | Requires a reusable probability model, expectation algebra, combinatorial symmetry, and asymptotics | Finish one Chapter 7 model end-to-end before sharing it with Chapters 8, 9, and 11 |
| Red-black deletion | Large case split over shape, colors, rotations, and black height | Stabilize one local fixup certificate per case before composing an executable algorithm |
| Imperative/RAM semantics | Introduces a new state and cost layer across many chapters | Treat it as an explicit refinement project, not an implicit condition on mathematical correctness |

## Scheduling Rule

Prefer a central missing theorem over additional helper lemmas in a sealed or
already mature chapter.  Any task should state its intended model, theorem
boundary, and verification target before implementation begins.
