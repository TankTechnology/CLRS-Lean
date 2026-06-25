# Blocked And Deferred Items

This page records work that is not hidden but also not claimed as complete.

## Deferred Implementation

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

### Union-Find Correctness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `deferred-implementation`
- Current decision: do not prove it in the first CLRS-Lean phase.

The current MST proof uses `ComponentOracle` and `CycleTestImplementation` as
interfaces.  A future union-find implementation can refine this interface
without changing the mathematical Kruskal proof.

## Blocked Design

### Hash-Table Expected-Time Analysis

- Related section: Section 11.2 - Chained hash tables
- Status: `blocked-design`

The deterministic chained-table interface is in place for a fixed hash
function, including insert/delete/search behavior.  The CLRS expected-time
theorem needs a probability model over keys, hash functions, or random
assignments before we can state simple uniform hashing precisely.

### Master Theorem Extension Beyond Exact Powers

- Related section: Section 4.5 - The master method
- Status: `future-work`

The exact-power recurrence expansion and three exact-power Master-style cases
are compiler-clean.  Section 4.6 now also proves floor/ceiling recurrence
interfaces, extracts exact-power recurrences from those all-input models, and
proves the generic transfer bridge from exact powers to all natural input sizes
under monotone-cost and power-sandwich hypotheses.  Section 4.6 also now proves
the adjacent-power `Nat.log` interval and derives both sandwich hypotheses from
monotone comparison scales with eventual one-step control.  It also proves the
discrete `criticalPowerScale` all-input wrapper for exact-power `Θ(a^i)`
bounds, including floor/ceiling recurrence wrappers for exact-power Master
case 1.  The remaining strengthening is to relate this bridge to analytic CLRS
comparison scales and package the remaining floor/ceiling statements.

### Remaining Chapter 4 Sections

- Related sections: Sections 4.2 and 4.6
- Status: `future-work`

These sections are not excluded from CLRS-Lean.  They are pending because they
need distinct representation choices: block matrices for Strassen and an
all-input floor/ceiling instantiation for the full Master Theorem.  Sections
4.3, 4.4, and 4.6 now provide reusable recurrence, recursion-tree, and
all-input transfer infrastructure, including adjacent-power sandwich generation
and a discrete critical-power all-input wrapper.

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
prefix-local sorted-order theorem, Prim's theorem interface, and any optional
union-find refinement.

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
postcondition, and `CLRS.Chapter07.quickSort_correct` packages sortedness plus
permutation preservation for the functional quicksort model.

The remaining CLRS refinements are harder.  The mutable-array `PARTITION` proof
needs a swap trace and an array segment invariant that tracks the less/equal
and greater regions while preserving the backing-list permutation.  Randomized
quicksort's expected running time needs a probability model for random pivots
or random permutations and a cost recurrence or indicator-variable proof.

### Chapter 8 Linear-Time Sorting Refinements

- Related sections: Sections 8.2-8.4 - Counting sort, radix sort, and bucket
  sort
- Status: `future-work` for count-array and numeric-order refinements;
  `blocked-design` for bucket-sort expected-time analysis

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

The remaining CLRS refinements split into three tracks.  The array-level
`COUNTING-SORT` proof should connect count arrays and prefix sums to the stable
bucket specification.  Radix sort still has implementation and cost refinement
work, but the bounded fixed-width ordinary key-order theorem is now proved.
Bucket-sort expected time needs a probability model for the input distribution,
so it remains a design-level proof task.

### Chapter 9 Selection Refinements

- Related sections: Sections 9.2-9.4 - Selection and order statistics
- Status: `future-work` for CLRS median-of-medians split-size/runtime
  refinements; `blocked-design` for randomized expected-time analysis

Section 9.2 proves the stable rank-certificate interface:
`CLRS.Chapter09.selectByRank?_correct` shows that the specification selector
returns an input value whose strict-lower count is at most the requested rank
and whose weak-lower count is greater than that rank.  The same certificate is
now proved for pivot-style quickselect by `CLRS.Chapter09.quickSelect?_correct`.
Section 9.3 factors the proof through a pivot-parametric deterministic SELECT
interface: `CLRS.Chapter09.selectWithPivot?_correct` proves correctness for any
membership-safe pivot rule, and `CLRS.Chapter09.deterministicSelect?_correct`
instantiates it with a deterministic median pivot.  It also proves
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
`CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`.

The remaining hard work splits into two tracks.  Randomized SELECT needs a
probability model for random pivots and an expected-cost argument.
Deterministic linear-time SELECT still needs the recurrence proof on top of the
proved `7n/10 + O(1)` partition-size theorem.

### Pointer-Level Linked Lists

- Related section: Section 10.2 - Linked lists
- Status: `future-work`

The current Section 10.2 file proves the functional-list membership behavior of
search, insertion, and deletion.  Predecessor/successor pointer updates,
sentinels, allocation, and free lists require a shared imperative memory model.

### Binary-Search-Tree Pointer Navigation And Transplant

- Related section: Section 12.1 - Binary search trees
- Status: `future-work`

Search, minimum/maximum, functional successor/predecessor, insertion, and
functional deletion membership/order preservation are proved.  The remaining
BST work is the CLRS parent-pointer, transplant, and mutation refinement layer.

### Full Red-Black Insertion And Deletion

- Related section: Section 13.1 - Red-black trees
- Status: `future-work`

The current Chapter 13 file proves local rotation, root recoloring, black-height
balance, and red-red repair certificates.  A full CLRS proof still needs
executable `RB-INSERT`, `RB-INSERT-FIXUP`, `RB-DELETE`, and `RB-DELETE-FIXUP`
together with preservation of the red-black invariants and height bound.
