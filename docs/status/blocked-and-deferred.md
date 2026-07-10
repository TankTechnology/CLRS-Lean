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
maximum, increase-key, extract-max, and delete.

The deferred implementation layer is now the line-by-line CLRS RAM-cost model,
not the array heap proof itself.

### Union-Find Cost And Stateful Kruskal Refinement

- Related sections: Sections 21.3-21.4 and 23.2
- Status: `deferred-implementation`
- Functional correctness status: proved for the represented Batteries model

Chapter 21 now proves singleton initialization, path-compressing `find`,
union-by-rank, and Boolean equivalence queries against a common partition
specification.  It also counts the real Batteries parent recursion, proves
rank mass for all states reachable by the costed operation machine, instantiates
the Ackermann level/index potential, and derives an `O((m+n) alpha(n))`
whole-run bound.  The Chapter 23 bridge proves that any family of faithful
union-find states implements `CycleTestImplementation`.

The deferred layer is an incremental stateful Kruskal scan, explicit write
charges beyond the proved parent-traversal model, and lower-level mutable-array
or RAM refinement.  The Section 21.4 inverse-Ackermann proof itself is closed.

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
Strassen and explicit algorithm/RAM cost models.  The current Master-theorem
comparison stack covers all three textbook cases under its stated assumptions.

### Maximum-Subarray Runtime Analysis

- Related section: Section 4.1 - The maximum-subarray problem
- Status: `future-work`

The exhaustive-search specification is now compiler-clean:
`CLRS.Chapter04.maxSubarray_correct` proves that the executable selector returns
a nonempty contiguous subarray of maximum sum.  The crossing-helper layer is
also compiler-clean:
`CLRS.Chapter04.maxCrossingSubarray_correct` proves optimality among candidates
crossing a split.  The combine-interface layer is compiler-clean as well:
`CLRS.Chapter04.subarray_append_left_or_right_or_crossing` classifies every
candidate as left-only, right-only, or crossing, and
`CLRS.Chapter04.subarray_append_optimal_of_cases` packages the corresponding
optimality argument.  The executable combine step
`CLRS.Chapter04.maxSubarrayDivideStep_correct` is now compiler-clean too.  The
recursive correctness layer is also compiler-clean:
`CLRS.Chapter04.maxSubarrayDivideTree_correct` proves the split-tree selector,
and `CLRS.Chapter04.maxSubarrayDivideFuel_correct` proves a fuelled midpoint
divide-and-conquer selector against the original input.  The remaining CLRS
refinement is runtime recurrence analysis and, eventually, a RAM-cost model for
the textbook pseudocode.

### Concrete MST Exchange Edge

- Related section: Section 23.1 - Growing a minimum spanning tree
- Status: `blocked-design`

The current theorem assumes a cut exchange certificate.  To remove that
assumption, we need a stable finite path or walk representation and a boundary
edge lemma for paths crossing a cut.

### Kruskal Exchange And Full Optimality Layer

- Related sections: Sections 23.1 and 23.2
- Status: `blocked-design` for concrete exchange paths; `partial` for the
  full recursive optimality wrapper

Kruskal's textbook proof relies on processing edges in nondecreasing weight.
The Lean proof now has a compiler-clean sorted-order lightness layer:
`CLRS.MST.lightest_crossing_of_sorted_prefix` proves that a sorted edge list
makes the current edge light once all crossing candidates are in the current
suffix, and `CLRS.MST.cut_certificate_of_component_oracle_sorted_prefix`
packages that fact as a component-oracle cut certificate.

The stronger exact-component layer is now compiler-clean as well:
`CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal` derives the
processed-prefix exclusion invariant for an actual Kruskal prefix, and
`CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix` packages it with
sorted edge order.  The finite-graph wrapper also proves the final-tree
obligation for complete exact-component scans from an initial forest:
`CLRS.MST.FiniteGraph.kruskal_subset_edges` and
`CLRS.MST.FiniteGraph.kruskal_spans_of_complete_exact_component`,
`CLRS.MST.FiniteGraph.kruskal_forest_of_exact_component`, and
`CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`.

The remaining MST gaps are the concrete path/cycle exchange edge, replacing the
global lightness hypothesis in the finite-graph optimality wrapper with the
prefix-local sorted-order theorem, Prim's theorem interface, and the stateful
union-find scan/cost refinement.

## Future Work

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
  `blocked-design` for the full bucket-sort expected-time theorem

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
`CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`.

The remaining CLRS refinements split into three tracks.  The array-level
`COUNTING-SORT` proof should connect count arrays and prefix sums to the stable
bucket specification.  Radix sort still has implementation and cost refinement
work, but the bounded fixed-width ordinary key-order theorem is now proved.
The remaining bucket-sort expected-time work is to connect that second-moment
interface to an explicit independent input distribution and a concrete
bucket-sort cost model.

### Chapter 9 Selection Refinements

- Related sections: Sections 9.2-9.4 - Selection and order statistics
- Status: `future-work` for CLRS median-of-medians runtime refinement;
  `blocked-design` for randomized expected-time analysis

Section 9.2 proves the stable rank-certificate interface:
`CLRS.Chapter09.selectByRank?_correct` shows that the specification selector
returns an input value whose strict-lower count is at most the requested rank
and whose weak-lower count is greater than that rank.  The same certificate is
now proved for pivot-style quickselect by `CLRS.Chapter09.quickSelect?_correct`.
Section 9.3 factors the proof through a pivot-parametric deterministic SELECT
interface: `CLRS.Chapter09.selectWithPivot?_correct` proves correctness for any
membership-safe pivot rule, `CLRS.Chapter09.deterministicSelect?_correct`
instantiates it with a deterministic median pivot, and
`CLRS.Chapter09.medianOfMediansSelect?_correct` instantiates it with an
executable median-of-medians pivot.  It also proves
`CLRS.Chapter09.medianOfFive?_certificate`, the local 3/3 count certificate for
a five-element group.  The executable grouping and grouped counting core are
now proved as well: `CLRS.Chapter09.fullGroupsOfFive_length_near`,
`CLRS.Chapter09.fullGroupsOfFive_flatten_sublist`,
`CLRS.Chapter09.leCount_le_of_sublist`,
`CLRS.Chapter09.geCount_le_of_sublist`,
`CLRS.Chapter09.medianOfFiveGroups?_certificates`,
`CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`,
`CLRS.Chapter09.medianGroupCertificates_leCount_lower_bound`,
`CLRS.Chapter09.medianGroupCertificates_geCount_lower_bound`, and
`CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`.  The
CLRS-style branch-size packaging is proved by
`CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`.

The remaining hard work splits into two tracks.  Randomized SELECT needs a
probability model for random pivots and an expected-cost argument.
Deterministic linear-time SELECT already has the abstract recurrence induction
and linear-bound wrapper; it still needs a concrete executable cost semantics
for `medianOfMediansSelect?` that feeds the proved recurrence hypothesis.

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
