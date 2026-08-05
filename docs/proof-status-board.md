# Proof Status Board

This board is the compact planning view for CLRS-Lean.  Chapter counts and
status labels come from [`clrs-proof-progress.csv`](clrs-proof-progress.csv).
The detailed theorem ledger is [`proof-map.md`](proof-map.md).  This page owns
priorities, not theorem-by-theorem duplication.

Last repository-wide status reconciliation: 2026-08-05.

Chapters 1--31 form a completed prefix for their advertised proof scopes.  The
prefix contains 12 `main-proof-complete` chapters, 11
`main-proof-complete-for-correctness` chapters, 7
`selected-section-complete` chapters, and the expository Chapter 1 guide.  The
generated dashboard owns the counts; the distinctions above prevent the prefix
milestone from being mistaken for complete coverage of every textbook section.

## Complete For The Current Scope

| Scope | Completed boundary | Refinements that do not reopen it |
| --- | --- | --- |
| Chapter 2 | Insertion sort, merge sort, and the all-input `Θ(n log n)` merge-sort recurrence bound | Full RAM semantics, explicit `List` allocation/copying, and exercises |
| Chapter 3 | Asymptotic wrappers, the standard-function comparison hierarchy, Fibonacci growth, and the iterated logarithm | Exercises and alternative asymptotic packaging |
| Chapter 4 | Maximum-subarray correctness and execution-attached abstract runtime `Θ(n log n)`, recursive Strassen correctness/runtime, and textbook-facing Master cases 1–3 | Explicit split-tree construction, integer operations, `List` allocation/copying, and RAM semantics |
| Chapter 5 represented sections | Hiring, indicators, random permutations, birthday collisions, balls-and-bins occupancy, expected longest streak `Θ(log n)`, and the on-line hiring harmonic closed form with its `1/e` asymptotic | Lower-level random sampling and RAM accounting |
| Chapter 6 | Heap predicate, heapify, build-heap, heapsort, represented priority-queue correctness, and costed executions with connected coarse `O(n)`, `O(n²)`, and `O(n²)` envelopes | Tight textbook bounds and List/RAM accounting |
| Chapter 7 represented sections | Functional/mutable-array quicksort correctness, comparison recurrences, pairwise comparison probability, `sum_compared_prob_eq_expectedComparisons`, and the `Θ(n log n)` bridge | Lower-level mutable-array execution costs and RAM accounting |
| Chapter 8 correctness | Represented counting-sort correctness with a mutable output-array (`Array`) refinement and linear `O(n + k)` work bound, radix-sort and bucket-sort correctness, the bucket-sort second moment, and the true linear expected CLRS unit-cost theorem (`expectedTextbookBucketSortCost_isBigO`) | Optional executable bucket-builder and execution-cost refinements |
| Chapter 9 | Pairwise extrema, rank-correct selection, schedule-driven RANDOMIZED-SELECT with nested conditional-uniform expectation and `E[C] ≤ 4*c*n`, and recursive median-of-medians SELECT with complete comparison cost `≤ 100n` | Random-number generator implementation, List primitives, allocation, and RAM accounting |
| Chapter 10 represented sections | Functional stacks, queues, linked lists, and the rooted-tree left-child/right-sibling isomorphism | Pointer memory and allocation |
| Chapter 11 correctness | Direct address, chaining with SUHA true expectations, universal hashing, open addressing, and perfect hashing | Probe-machine/RAM operational semantics |
| Chapter 12 correctness | Functional BSTs, zipper navigation/transplant, and represented pointer-heap transplant/insert refinements | In-place pointer delete and RAM accounting |
| Chapter 13 correctness | Executable red-black insertion and deletion with exact membership correctness, red-black shape preservation (`redBlackShape_insert`, `redBlackShape_delete` via the `baldL`/`baldR`/`splitMin`/`join` rebalancing pipeline), and the logarithmic-height theorem (CLRS Lemma 13.1) | Pointer-level mutation and RAM cost semantics |
| Chapter 14 correctness | Order-statistic tree operations with `wellSized_insert`/`wellSized_delete`, interval-tree search with `maxHighAug`, the general augmentation theorem, and generic `AugmentedRBTree` insertion/deletion with `wellAugmented_delete` and `toRB_delete` erasure | Pointer-level mutation and RAM cost semantics |
| Chapter 15 represented sections | Rod cutting, matrix chain, LCS, and optimal BST optimality with executable recurrence/reconstruction layers | Additional mutable-array/RAM refinements |
| Chapter 16 | Activity selection, greedy meta-theorems, Huffman coding, matroid greedy, and task scheduling | Exercises |
| Chapter 17 selected sections | Aggregate/accounting/potential methods, stack/counter traces, and dynamic-table amortized analysis | General allocator/RAM semantics and broader interleaved operation-trace packaging |
| Chapter 18 correctness | B-tree search, real top-level insertion with full-root splitting, exact executable deletion, structural minimum-key bounds with an explicit legal-empty-root branch, and the logarithmic-height theorem for `2 ≤ t` | Disk pages, pointer mutation, I/O counts, and RAM costs |
| Chapter 19 correctness and amortized analysis | Persistent executable Fibonacci heaps with exact duplicate-preserving key bags, `LINK`/`CONSOLIDATE`, extract-min, arbitrary-node cascading cuts, decrease-key/delete, and operation- plus trace-level amortized bounds | Mutable circular-list allocation and RAM/pointer latency |
| Chapter 20 correctness | All seven operations of the recursive cached-min/max vEB model and control-flow-aware `O(log log u)` bounds | Concrete allocation and hardware-level RAM timing |
| Chapter 21 | Partition semantics, weighted linked-list analysis, executable Batteries union-find, reachable rank mass, and `O((m+n) alpha(n))` amortization | Lower-level RAM constants and mutable-array refinement |
| Chapter 22 correctness | BFS shortest paths/predecessor tree, DFS theory, Kahn and DFS topological sorts, Kosaraju SCC partition | Work counts, `O(V + E)`, and imperative/RAM refinement |
| Chapter 23 correctness and functional implementation | Cut property, unique tree paths, automatic exchange, sorted and stateful Kruskal, concrete indexed-queue Prim, and explicit algorithm-level work bounds | `Batteries.BinaryHeap` array refinement and mutable/RAM write accounting |
| Chapter 24 selected sections | Bellman-Ford, DAG shortest paths, Dijkstra's greedy theorem and executable loop, difference constraints, and the no-path, upper-bound, and triangle-inequality shortest-path properties | Subpath, convergence/path-relaxation, predecessor-subgraph, and mutable/RAM refinements |
| Chapter 25 correctness | FASTER-APSP, Floyd-Warshall shortest distances, predecessor reconstruction with walk and weight guarantees, negative-cycle detection, transitive closure, and Johnson's end-to-end correctness theorem | A tighter explicit repeated-squaring work/RAM refinement |
| Chapter 26 | Max-Flow Min-Cut, executable residual BFS and Edmonds-Karp, the `O(VE²)` augmentation bound, and maximum bipartite matching through Theorem 26.12 | Sections 26.4 and 26.5 are deferred outside the current selected milestone |
| Chapter 27 | Pure-functional main text through Section 27.3: total greedy scheduling, logarithmic parallel loops, executable P-ADD/P-MATMUL, and executable P-MERGE/P-MERGE-SORT with correctness, execution costs, and matching worst-case span witnesses | Mutable-array/RAM realization, exercises, and chapter-end problems; parallel Strassen remains a separate compatibility extension |
| Chapter 28 | LUP decomposition (Theorem 28.1), LUP-SOLVE correctness, forward/backward substitution (Lemmas 28.1-28.2), matrix inversion (Theorem 28.2), Cholesky decomposition (Theorem 28.3) with uniqueness, and least-squares approximation (Theorem 28.4) | Executable LUP factorization from `A`; RAM cost semantics |
| Chapter 29 | Sections 29.1--29.5: standard/slack equivalence; four textbook LP formulations; exact PIVOT, Bland anti-cycling, and terminating SIMPLEX; weak/strong duality and complementary slackness; phase-I initialization and the certified three-way solver | Mutable tableau storage, floating-point numerical analysis, RAM constants, exercises, and chapter-end problems |
| Chapter 30 | Sections 30.1--30.3: polynomial representations, generic DFT algebra, recursive and iterative radix-2 FFT correctness, FFT multiplication, execution-attached `Theta(n log n)` work, and evaluated layered-circuit size/depth | Optional extensions only (zero missing core groups): mutable/in-place arrays, RAM/cache/hardware costs, floating-point error, concrete scheduling, NTT/code generation, exercises, and Problems 30-1 through 30-6 |
| Chapter 31 represented sections | Sections 31.1--31.9: elementary number theory, Euclid and extended Euclid, modular arithmetic and congruences, CRT, powers, RSA, primality testing, and factorization | Running-time analysis, general CRT, Miller--Rabin, and full Pollard-rho probability analysis |
| Chapter 32.1 | String-model facts plus soundness and completeness of the naive matcher | Sections 32.2--32.4 |

Chapter 9 and Chapters 21-23 are formally sealed by their interface tests and
dated closure audits.  Their listed implementation refinements are new layers,
not missing core theorem groups.

## Structured But Partial

| Chapter | Strongest current layer | Central remaining group |
| --- | --- | --- |
| 33 | Section 33.1 point/vector and line-segment definitions, six cross-product algebra theorems, and `orientation_spec` | Prove `segmentIntersect` soundness and completeness against an independent geometric-intersection specification, including shared-endpoint cases |

## Not Represented On Main

- Chapters 34--35.

Open branches and pull requests are intentionally excluded until they are
reviewed, merged, registered in `literate.toml`, and added to the progress CSV.

## High-Difficulty Queue

| Scope | Why it is difficult | Recommended boundary |
| --- | --- | --- |
| Imperative/RAM semantics | Introduces a new state and cost layer across many chapters | Treat it as an explicit refinement project, not an implicit condition on mathematical correctness |

## Scheduling Rule

Prefer a central missing theorem over additional helper lemmas in a sealed or
already mature chapter.  Any task should state its intended model, theorem
boundary, and verification target before implementation begins.
