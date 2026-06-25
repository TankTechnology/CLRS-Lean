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
are compiler-clean.  The remaining strengthening is to extend the theorem from
inputs `n = b^i` to arbitrary natural input sizes using a monotone recurrence
model and floor/ceiling sandwiching.

### Remaining Chapter 4 Sections

- Related sections: Sections 4.2 and 4.6
- Status: `future-work`

These sections are not excluded from CLRS-Lean.  They are pending because they
need distinct representation choices: block matrices for Strassen and an
all-input floor/ceiling bridge for the full Master Theorem.  Sections 4.3 and
4.4 now provide the reusable recurrence and recursion-tree infrastructure.

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

### Quicksort In-Place Partition And Randomized Analysis

- Related sections: Sections 7.2-7.4 - Quicksort performance and randomized
  quicksort
- Status: `future-work` for in-place partition; `blocked-design` for expected
  randomized analysis

Section 7.1 proves the functional partition/quicksort correctness spine:
`CLRS.Chapter07.partitionAround_perm` proves that partition preserves exactly
the input tail elements, and `CLRS.Chapter07.quickSort_correct` packages
sortedness plus permutation preservation for the functional quicksort model.

The remaining CLRS refinements are harder.  The in-place `PARTITION` proof
needs an array segment invariant that tracks the less/equal and greater
regions while preserving the backing-list permutation.  Randomized quicksort's
expected running time needs a probability model for random pivots or random
permutations and a cost recurrence or indicator-variable proof.

### Chapter 8 Linear-Time Sorting Refinements

- Related sections: Sections 8.2-8.4 - Counting sort, radix sort, and bucket
  sort
- Status: `future-work` for count-array and numeric-digit refinements;
  `blocked-design` for bucket-sort expected-time analysis

Section 8.2 proves the stable bucket specification for counting sort:
`CLRS.Chapter08.countingSortBy_ordered` proves ordered output by key,
`CLRS.Chapter08.countingSortBy_bucket_eq` proves exact preservation of every
equal-key subsequence, and `CLRS.Chapter08.countingSortBy_correct` packages the
reader-facing correctness theorem.  Section 8.3 proves abstract radix-sort
correctness: `CLRS.Chapter08.radixPass_orderedRel` is the stable digit-pass
lemma, and `CLRS.Chapter08.radixSortBy_correct` packages lexicographic ordering
plus membership preservation.

The remaining CLRS refinements split into three tracks.  The array-level
`COUNTING-SORT` proof should connect count arrays and prefix sums to the stable
bucket specification.  Radix sort still needs a concrete base-`b` digit
extraction refinement from natural-number keys to the abstract digit-function
interface.  Bucket-sort expected time needs a probability model for the input
distribution, so it is a design-level proof task rather than a small
deterministic lemma.

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
