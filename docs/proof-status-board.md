# Proof Status Board

This board is the compact planning view for CLRS-Lean.  Chapter counts and
status labels come from [`clrs-proof-progress.csv`](clrs-proof-progress.csv).
The detailed theorem ledger is [`proof-map.md`](proof-map.md).  This page owns
priorities, not theorem-by-theorem duplication.

Last repository-wide status reconciliation: 2026-07-15.

## Complete For The Current Scope

| Scope | Completed boundary | Refinements that do not reopen it |
| --- | --- | --- |
| Chapter 2 | Insertion sort, merge sort, and represented cost/recurrence results | Full RAM semantics and arbitrary-size merge-sort recurrence |
| Chapter 3 | Asymptotic wrappers, the standard-function comparison hierarchy, Fibonacci growth, and the iterated logarithm | Exercises and alternative asymptotic packaging |
| Chapter 4 | Maximum-subarray correctness and execution-attached abstract runtime `Θ(n log n)`, recursive Strassen correctness/runtime, and textbook-facing Master cases 1–3 | Explicit split-tree construction, integer operations, `List` allocation/copying, and RAM semantics |
| Chapter 5 represented sections | Hiring, indicators, random permutations, birthday collisions, balls-and-bins occupancy, the longest-streak tail bound, and an executable on-line hiring strategy | Expected-longest-streak and on-line hiring asymptotics remain chapter-end Problems |
| Chapter 6 | Heap predicate, heapify, build-heap, heapsort, represented priority-queue correctness, and costed executions with connected coarse `O(n)`, `O(n²)`, and `O(n²)` envelopes | Tight textbook bounds and List/RAM accounting |
| Chapter 8 correctness | Represented counting-sort correctness with a mutable output-array (`Array`) refinement and linear `O(n + k)` work bound, radix-sort and bucket-sort correctness, the bucket-sort second moment, and the true linear expected CLRS unit-cost theorem (`expectedTextbookBucketSortCost_isBigO`) | Optional executable bucket-builder and execution-cost refinements |
| Chapter 9 | Pairwise extrema, rank-correct selection, schedule-driven RANDOMIZED-SELECT with nested conditional-uniform expectation and `E[C] ≤ 4*c*n`, and recursive median-of-medians SELECT with complete comparison cost `≤ 100n` | Random-number generator implementation, List primitives, allocation, and RAM accounting |
| Chapter 10 represented sections | Functional stacks, queues, linked lists, and the rooted-tree left-child/right-sibling isomorphism | Pointer memory and allocation |
| Chapter 11 correctness | Direct address, chaining with SUHA true expectations, universal hashing, open addressing, and perfect hashing | Probe-machine/RAM operational semantics |
| Chapter 12 correctness | Functional BSTs, zipper navigation/transplant, and represented pointer-heap transplant/insert refinements | In-place pointer delete and RAM accounting |
| Chapter 15 represented sections | Rod cutting, matrix chain, LCS, and optimal BST optimality with executable recurrence/reconstruction layers | Additional mutable-array/RAM refinements |
| Chapter 16 | Activity selection, greedy meta-theorems, Huffman coding, matroid greedy, and task scheduling | Exercises |
| Chapter 17 represented sections | Aggregate/accounting/potential methods, stack/counter traces, and dynamic-table amortized analysis | Allocator constants and RAM refinement |
| Chapter 20 correctness | All seven operations of the recursive cached-min/max vEB model and control-flow-aware `O(log log u)` bounds | Concrete allocation and hardware-level RAM timing |
| Chapter 21 | Partition semantics, weighted linked-list analysis, executable Batteries union-find, reachable rank mass, and `O((m+n) alpha(n))` amortization | Lower-level RAM constants and mutable-array refinement |
| Chapter 22 correctness | BFS shortest paths/predecessor tree, DFS theory, Kahn and DFS topological sorts, Kosaraju SCC partition | Work counts, `O(V + E)`, and imperative/RAM refinement |
| Chapter 23 correctness and functional implementation | Cut property, unique tree paths, automatic exchange, sorted and stateful Kruskal, concrete indexed-queue Prim, and explicit algorithm-level work bounds | `Batteries.BinaryHeap` array refinement and mutable/RAM write accounting |

Chapter 9 and Chapters 21-23 are formally sealed by their interface tests and
dated closure audits.  Their listed implementation refinements are new layers,
not missing core theorem groups.

## Structured But Partial

| Chapter | Strongest current layer | Central remaining group |
| --- | --- | --- |
| 7 | Functional quicksort correctness, comparison recurrence, harmonic bounds, plus the random-permutation symmetry lemma (`isFirst_prob`) and pairwise comparison probability (`compared_prob = 2/(j-i+1)`, CLRS Theorem 7.3) over the shared `Probability.FiniteExpectation` toolkit | End-to-end total-comparison expectation (`expected_comparisons_eq_sum`) and the `Θ(n log n)` asymptotic bridge |
| 13 | Executable insertion, the logarithmic-height theorem, executable deletion with exact membership correctness, and local delete-fixup certificates | `RedBlackShape` preservation through the composed `del`/`delete` pipeline |
| 14 | Order-statistic augmentation, the general augmentation theorem (CLRS Theorem 14.1), interval-search correctness, and the size invariant threaded through executable red-black insertion (`OSRBTree.wellSized_insert`, refining Chapter 13 `RBTree.insert` via `toRB_insert`) | Stored-field refinement through executable red-black deletion |
| 18 | Mathematical B-tree search/split/insert/delete specs | Separator/occupancy/same-depth invariants and deletion repair |
| 19 | Finite-set operation specs, potential facts, and the concrete rooted-tree logarithmic degree theorem | Executable heap-forest consolidation/cascading cuts and their amortized costs |
| 24 | Bellman-Ford, DAG SSSP, Dijkstra greedy theory and state/step/loop skeleton, plus difference constraints | Repair the initialization/invariant boundary and prove final Dijkstra distance correctness |
| 25 | Correct FASTER-APSP; Floyd-Warshall definitions/work; Johnson reweighting algebra | Floyd-Warshall correctness, path reconstruction/negative cycles, and end-to-end Johnson correctness |
| 26 | Flow model, generic Ford-Fulkerson maximality direction, MFMC easy direction, and Edmonds-Karp Lemma 26.7 | MFMC converse, executable Edmonds-Karp with `O(VE²)`, and Section 26.3 matching reduction |
| 27 | Computation-DAG/spawn-tree model with honest span and `T∞ ≤ T₁`; executable work/span recurrences for P-MATMUL, P-MERGE, P-MERGE-SORT, and parallel Strassen with exact power-of-two closed forms (work `Θ(n³)`/`Θ(n)`/`Θ(n log n)`/`Θ(n^(log₂ 7))`, spans `Θ(log n)`/`Θ(log² n)`/`Θ(log³ n)`) plus all-input P-MATMUL bounds | Greedy-scheduler bound (Theorem 27.1/27.2), all-input Θ-bounds for the merge-based costs, and executable algorithm refinements |

## Not Represented On Main

- Chapters 28-35.

Open branches and pull requests are intentionally excluded until they are
reviewed, merged, registered in `literate.toml`, and added to the progress CSV.

## Next Proof Plan

| Priority | Target | Concrete deliverable |
| --- | --- | --- |
| 0 | Chapter 24 Dijkstra closure | Align `dijkstraInit` with `DijkstraInvariant`, lift the invariant through `dijkstraLoop`, and prove the final distance map equals `δ` |
| 1 | Chapter 25 correctness | Prove Floyd-Warshall first; then close Johnson and the predecessor/negative-cycle interfaces |
| 2 | Chapter 26 correctness | Prove the MFMC converse, then the Edmonds-Karp counting theorem and bipartite-matching reduction |
| 3 | Chapter 13/14 tree integration | Prove composed red-black deletion shape preservation, then transport augmentation through deletion |
| 4 | Chapter 7 randomized analysis | Build the total-comparison random variable and expectation-sum bridge |

## High-Difficulty Queue

| Scope | Why it is difficult | Recommended boundary |
| --- | --- | --- |
| Randomized expected-time analysis | Requires a reusable probability model, expectation algebra, combinatorial symmetry, and asymptotics | Reuse Chapter 9's fresh-choice finite expectation and pointwise continuation coupling for Chapter 7's end-to-end comparison expectation |
| Red-black deletion | Large case split over shape, colors, rotations, and black height | Stabilize one local fixup certificate per case before composing an executable algorithm |
| Imperative/RAM semantics | Introduces a new state and cost layer across many chapters | Treat it as an explicit refinement project, not an implicit condition on mathematical correctness |

## Scheduling Rule

Prefer a central missing theorem over additional helper lemmas in a sealed or
already mature chapter.  Any task should state its intended model, theorem
boundary, and verification target before implementation begins.
