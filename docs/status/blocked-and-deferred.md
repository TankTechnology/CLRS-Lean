# Blocked And Deferred Items

This page records work that is not hidden but also not claimed as complete.

## Deferred Implementation

### Union-Find Correctness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `deferred-implementation`
- Current decision: do not prove it in the first CLRS-lean phase.

The current MST proof uses `ComponentOracle` and `CycleTestImplementation` as
interfaces.  A future union-find implementation can refine this interface
without changing the mathematical Kruskal proof.

## Blocked Design

### Hash-Table Expected-Time Analysis

- Related section: Section 11.2 - Chained hash tables
- Status: `blocked-design`

The deterministic chained-table interface is in place for a fixed hash
function.  The CLRS expected-time theorem needs a probability model over keys,
hash functions, or random assignments before we can state simple uniform
hashing precisely.

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

### Binary-Search-Tree Deletion And Navigation

- Related section: Section 12.1 - Binary search trees
- Status: `future-work`

Insertion membership and ordering preservation are proved.  Search,
minimum/maximum, successor/predecessor, transplant, and deletion are the next
functional-tree layer before any pointer-level refinement.

### Full Red-Black Insertion And Deletion

- Related section: Section 13.1 - Red-black trees
- Status: `future-work`

The current Chapter 13 file proves local rotation and recoloring lemmas.  A
full CLRS proof still needs executable `RB-INSERT`, `RB-INSERT-FIXUP`,
`RB-DELETE`, and `RB-DELETE-FIXUP` together with preservation of the red-black
invariants and height bound.
