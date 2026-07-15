# Blocked And Deferred Items

This page records work that is not hidden but also not claimed as complete.

## Deferred Implementation

### Chapter 22 Work And RAM-Cost Refinement

- Related sections: Sections 22.1-22.5 - Elementary graph algorithms
- Status: `deferred-implementation`
- Core correctness status: sealed by the Chapter 22 closure audit

The finite-graph functional models now prove BFS reachability, exact unweighted
shortest distances and predecessor-tree correctness; DFS white-path,
parenthesis, ancestry, and edge-classification theorems; Kahn and DFS
finish-time topological sorting; and Kosaraju SCC-partition correctness.

The deferred layer is explicit work accounting and a lower-level adjacency-list
or RAM refinement, including textbook `O(V + E)` packaging.  This work may be
added without reopening the main functional-correctness milestone.

### Chapter 6 RAM-Cost Refinement

- Related section: Sections 6.1-6.5 - Heapsort and priority queues
- Status: `deferred-implementation`

The current Chapter 6 proof no longer treats the functional descending-list
heap as the main result.  It proves the indexed array heap layer, recursive
fuelled `MAX-HEAPIFY`, bottom-up `BUILD-MAX-HEAP`, in-place heapsort with a
shrinking heap prefix and sorted suffix, top-level heapsort sortedness and
permutation preservation, and array-level priority-queue state theorems for
maximum, increase-key, extract-max, and delete.  The connected costed execution
now mirrors heapify, build-heap, and heapsort and proves coarse `O(n)`,
`O(n^2)`, and `O(n^2)` envelopes after erasing the cost component.

The proved unit control-step metric counts visited `MAX-HEAPIFY` frames and
one extraction/swap transition per nontrivial heapsort step.  Build-loop
orchestration, guards, `List` operations, allocation, and calls are not charged
separately.  The deferred layer is therefore the tight textbook `O(log n)`,
`O(n)`, and `O(n log n)` analysis plus a line-by-line imperative array/RAM
refinement, not the array heap or erasure proof itself.

### Chapter 4.1 Maximum-Subarray Low-Level Cost Refinement

- Related section: Section 4.1 - The maximum-subarray problem
- Status: `deferred-implementation`
- Functional and algorithm-level runtime status: proved

`CLRS.Chapter04.maxSubarrayDivideCosted` measures the executable midpoint
divide-and-conquer selector that uses linear prefix, suffix, and crossing
scans.  `CLRS.Chapter04.maxSubarrayDivideCosted_result` proves cost erasure,
`CLRS.Chapter04.maxSubarrayDivideCosted_correct` proves result correctness,
and `CLRS.Chapter04.maxSubarrayDivideCosted_cost_eq` identifies the measured
cost with the length-indexed recurrence.  Its mixed floor/ceiling unfolding is
`CLRS.Chapter04.maxSubarrayDivideCost_unfold`, and
`CLRS.Chapter04.maxSubarrayDivideCost_isBigTheta_nlogn` proves the all-input
`Theta(n log n)` bound.

The proved metric counts recursive frames, scan transitions, and constant-size
candidate choices.  It does not charge construction of the explicit split
tree, integer arithmetic, `List` allocation/copying, or garbage collection.
The deferred layer is a lower-level direct recursion or imperative array/RAM
refinement with those operations attached; the CLRS algorithm-level runtime is
not deferred.

### Chapter 9 RANDOMIZED-SELECT Low-Level Cost Refinement

- Related section: Section 9.2 - Selection in expected linear time
- Status: `deferred-implementation`
- Functional and partition-work status: proved

`randomizedSelectCostWithSchedule` now consumes one occurrence-rank choice per
visited recursive state, charges `c * currentLength`, rejects exhausted or
out-of-range schedules, and erases successful runs to rank-correct SELECT.
`randomizedSelectExpectedCostFuel` samples a fresh uniform rank from the current
`Fin n` at each level; `randomizedSelectExpectedCost_le_randSelectExpectedCost`
couples that nested process to the CLRS larger-side recurrence, and
`randomizedSelectExpectedCost_linear_bound` proves `E[C] ≤ 4 * c * n`.

The deferred layer is lower-level execution accounting: a concrete RNG,
mutable in-place partitioning, costs of `List` primitives and the
`selectByRank?` specification sorter, allocation, and RAM operations.  The
proved expectation is recursively conditional-uniform; it is not stated as a
flat uniform expectation over variable-length schedules.

### Chapter 23 Mutable Heap And RAM Refinement

- Related sections: Sections 21.3-21.4 and 23.2
- Status: `deferred-low-level-implementation`
- Functional correctness and algorithm-level cost status: proved

Chapter 21 now proves singleton initialization, path-compressing `find`,
union-by-rank, and Boolean equivalence queries against a common partition
specification.  It also counts the real Batteries parent recursion, proves
rank mass for all states reachable by the costed operation machine, instantiates
the Ackermann level/index potential, and derives an `O((m+n) alpha(n))`
whole-run bound.  The Chapter 23 bridge proves that any family of faithful
union-find states implements `CycleTestImplementation`.

Chapter 23 now incrementally threads that real costed machine through every
Kruskal edge, proves connectivity faithfulness after each union, and derives
both the inverse-Ackermann scan term and the complete sorting-plus-scan
`O(E log E)` bound.  Prim now has an executable indexed queue with keys,
parents, decrease-key, extract-min, a concrete frontier provider, refinement
to `PrimTrace`, and a binary-heap operation-count proof of `O(E log V)`.

The deferred layer is narrower: refine the indexed Prim queue to the concrete
array state of `Batteries.BinaryHeap`, and add explicit mutable-array write and
RAM charges.  The mathematical and functional algorithm proofs are closed.

## Blocked Design

### Hash-Table Expected-Time Analysis

- Related section: Section 11.2 - Chained hash tables
- Status: `blocked-design`

The deterministic chained-table interface is in place for a fixed hash
function, including insert/delete/search behavior.  The CLRS expected-time
theorem needs a probability model over keys, hash functions, or random
assignments before we can state simple uniform hashing precisely.

### Master Theorem Generalization Beyond The Current Assumptions

- Related section: Section 4.5 - The master method
- Status: `future-work`

The exact-power cases, floor/ceiling transfer, adjacent-power sandwich, and
textbook-facing comparison scales for cases 1, 2, and regular case 3 are
compiler-clean.  Future work may weaken assumptions or package additional
variants, but there is no remaining core case-3 comparison gap.

### Remaining Chapter 4 Sections

- Related sections: Sections 4.2 and 4.6
- Status: `future-work`

These sections are not excluded from CLRS-Lean.  The remaining refinements need
distinct representation choices: general-size recursive block matrices for
Strassen and lower-level representation/RAM cost models.  The current
Master-theorem comparison stack covers all three textbook cases under its
stated assumptions, and Section 4.1's executable abstract runtime is complete.

## Future Work

### Chapter 5.4 Longest-Streak And On-Line Hiring Analysis

- Related section: Section 5.4 - Probabilistic analysis of randomized algorithms
- Status: `future-work`

The finite foundations are present.  The streak model proves
`CLRS.Chapter05.longestStreak_upperBound` and defines
`CLRS.Chapter05.expectedLongestStreak`.  The on-line hiring model provides an
executable threshold strategy, exact `some`/`none` contracts, and the finite
uniform success probability `CLRS.Chapter05.OnlineHiring.probHireBest`.

Two textbook-facing analyses remain: derive the logarithmic expectation bound
for the longest streak, and prove the on-line strategy's harmonic success
formula together with its `1/e` asymptotic.  These theorem gaps do not block use
of either executable finite model.

### CLRS Exercises

- Related scope: all chapters
- Status: `future-work`

Exercises should be recorded after the main theorem interface for a section is
stable.  This keeps the first pass focused on core textbook claims while still
leaving a clear path for a richer companion project.

### Chapter-End Problems

- Related scope: all chapters
- Status: `future-work`

Chapter-end Problems should become a separate track with explicit priority and
difficulty labels.  Some Problems are small theorem variations; others are
mini-projects and should not block the main chapter workflow.

### Full RAM Semantics

- Related scope: analysis-of-algorithms chapters
- Status: `future-work`

A full RAM semantics would model CLRS-style imperative pseudocode with machine
states, arrays or memory, variables/registers, control flow, primitive
operations, and per-step costs.  It is stronger than the current lightweight
cost models, which prove mathematical recurrences and bounds directly.

### General Merge-Sort Recurrence

- Related section: Section 2.3 - Designing algorithms
- Status: `future-work`

The power-of-two recurrence is proved.  The arbitrary-size recurrence
`T(n) = T(⌈n / 2⌉) + T(⌊n / 2⌋) + n` remains future work because it needs
floor/ceiling arithmetic, monotonicity, and a clean asymptotic theorem for all
input sizes.

### Quicksort Mutable-Array Partition And Randomized Analysis

- Related sections: Sections 7.2-7.4 - Quicksort performance and randomized
  quicksort
- Status: `future-work` for mutable-array partition refinement;
  `blocked-design` for expected randomized analysis

Section 7.1 proves the functional partition/quicksort correctness spine:
`CLRS.Chapter07.partitionAround_correct` proves stable-filter partition
classification plus permutation preservation,
`CLRS.Chapter07.partitionLoop_correct` proves a scan-state partition-loop
invariant and connects it to the stable partition specification,
`CLRS.Chapter07.clrsPartitionArray_correct` packages the returned pivot-index
postcondition, `CLRS.Chapter07.clrsPartitionArray_correct_with_trace` adds an
explicit adjacent-swap trace, and `CLRS.Chapter07.quickSort_correct` packages
sortedness plus permutation preservation for the functional quicksort model.

The remaining CLRS refinements are harder.  The mutable-array `PARTITION` proof
needs an index-level array segment invariant that tracks the less/equal and
greater regions while preserving the backing-list permutation.  The
expected-comparison recurrence and harmonic bound are already proved in the
current model; the remaining randomized-analysis layer is deriving that model
from an explicit probability space for random pivots or random permutations.

### Chapter 8 Linear-Time Sorting Refinements

- Related sections: Sections 8.2-8.4 - Counting sort, radix sort, and bucket
  sort
- Status: `future-work` for count-array and numeric-order refinements;
  `proved-abstract` for the bucket-sort textbook cost model, with executable
  cost refinement still `future-work`

Section 8.2 proves the stable bucket specification for counting sort:
`CLRS.Chapter08.countingSortBy_ordered` proves ordered output by key,
`CLRS.Chapter08.countingSortBy_bucket_eq` proves exact preservation of every
equal-key subsequence, `CLRS.Chapter08.countingSortBy_perm` proves multiset
preservation, and `CLRS.Chapter08.countingSortBy_correct` packages the
reader-facing correctness theorem.  Section 8.3 proves abstract radix-sort
correctness: `CLRS.Chapter08.radixPass_orderedRel` is the stable digit-pass
lemma, `CLRS.Chapter08.radixSortBy_stable` proves complete digit-signature
stability, `CLRS.Chapter08.radixSortBy_perm` proves repeated passes preserve
the input as a permutation, and `CLRS.Chapter08.radixSortBy_correct_stable`
packages lexicographic ordering, stability, membership preservation, and
permutation preservation.  It also instantiates the abstract digit interface
with concrete natural-number base-`b` digits through
`CLRS.Chapter08.baseDigitsLow_allDigitsLe` and
`CLRS.Chapter08.radixSortNatBy_correct_stable`, packages ordinary key ordering
through `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder`, and
proves the bounded fixed-width key-order bridge by
`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded`.  Section 8.4
proves deterministic bucket-sort correctness:
`CLRS.Chapter08.bucketSortByRank_correct` packages ordered output, membership
preservation, and permutation preservation for the merge-sorted bucket model.
It also proves the finite-uniform collision and second-moment core:
`CLRS.Chapter08.uniformAverageFin2_collision` and
`CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`.  The CLRS
unit-cost random variable is `CLRS.Chapter08.textbookBucketSortCost`; its
expectation is identified by
`CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`
and proved linear by
`CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO`.

The remaining CLRS refinements split into three tracks.  The array-level
`COUNTING-SORT` proof should connect count arrays and prefix sums to the stable
bucket specification.  Radix sort still has implementation and cost refinement
work, but the bounded fixed-width ordinary key-order theorem is now proved.
For bucket sort, the CLRS unit-cost random variable has linear expectation.
Remaining: a single-pass executable bucket builder, a costed per-bucket sorter,
and a refinement theorem connecting their execution cost to the abstract
model.  The current `bucketSortByRank` repeatedly filters the input and is not
instrumented by this abstract random variable.

### Pointer-Level Linked Lists

- Related section: Section 10.2 - Linked lists
- Status: `future-work`

The current Section 10.2 file proves the functional-list membership behavior of
search, insertion, and deletion.  Predecessor/successor pointer updates,
sentinels, allocation, and free lists require a shared imperative memory model.

### Binary-Search-Tree Pointer-Level Mutation

- Related section: Section 12.1 - Binary search trees
- Status: `deferred-implementation`

Search, minimum/maximum, functional successor/predecessor, insertion, and
functional deletion membership/order preservation are proved.  A zipper-based
parent-pointer layer is now also proved: iterative search
(`searchIter_eq_search`), `TRANSPLANT` ordering preservation
(`transplant_preserves_ordered`), `TREE-DELETE` via transplant
(`deleteViaTransplant_eq_delete`), and parent-pointer successor/predecessor
(`successorZipper_eq_successor?`, `predecessorZipper_eq_predecessor?`), each
proved equivalent to the functional operation.  The remaining BST work is the
imperative in-place pointer-mutation (RAM) refinement.

### Red-Black Deletion And Height

- Related section: Section 13.1 - Red-black trees
- Status: `future-work`

The current Chapter 13 file includes executable insertion with membership,
shape, and black-height theorems.  The remaining CLRS proof layer is executable
`RB-DELETE`, `RB-DELETE-FIXUP`, invariant preservation, and the logarithmic
height bound.
