# Blocked And Deferred Items

This page records work that is not hidden but also not claimed as complete.

## Deferred Implementation

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

### Maximum-Subarray Divide-And-Conquer Refinement

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
remaining CLRS refinement is to thread that step through a full recursive
selector and add its runtime recurrence.

### Concrete MST Exchange Edge

- Related section: Section 23.1 - Growing a minimum spanning tree
- Status: `blocked-design`

The current theorem assumes a cut exchange certificate.  To remove that
assumption, we need a stable finite path or walk representation and a boundary
edge lemma for paths crossing a cut.

### Sorted-Order Lightness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `partial`

Kruskal's textbook proof relies on processing edges in nondecreasing weight.
The Lean proof still needs a processed-prefix invariant showing that any lighter
crossing edge would already have been considered and rejected.

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
