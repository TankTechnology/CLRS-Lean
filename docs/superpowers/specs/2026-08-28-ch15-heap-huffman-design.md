# Chapter 15 Verified Heap Huffman Design

## Goal

Close issue #338 by making the textbook `O(n log n)` Huffman claim a theorem
about one executable program.  The program must initialize a binary min-heap,
perform two `EXTRACT-MIN` operations and one `INSERT` per merge, return the
same Huffman tree as the already verified sorted-list implementation, and
carry an operation count bounded by `O(n log n)`.

## Semantic decision: make tie handling explicit

The existing `insortTree` inserts a new tree before every tree with equal root
frequency.  A heap that compares only frequencies may choose another equal
frequency tree and therefore need not return definitionally the same tree,
even though its result is still optimal.

Each heap entry therefore contains:

```lean
structure HeapEntry where
  tree : HuffTree
  stamp : Nat
```

Its priority is the lexicographic pair `(rootFreq tree, stamp)`.  For an input
of length `n`, initial leaves receive stamps `n, n + 1, ...`; when a queue of
length `m >= 2` merges its two minima, the new inner node receives stamp
`m - 2`.  Thus all stamps are distinct, initial equal-frequency leaves retain
input order, and every newly merged node precedes all older equal-frequency
entries.  Erasing stamps from priority order exactly recovers `sortForest` and
`insortTree`.

## Executable heap

The implementation is an array-shaped binary min-heap, represented by a
`List HeapEntry` so its permutation proofs compose with the rest of the
repository.  It uses the Chapter 6 index functions `parent`, `left`, and
`right`, and follows the same algorithms as `Batteries.BinaryHeap`:

- insertion appends one entry and repeatedly swaps it with its parent;
- extraction swaps the root with the last entry, removes the last cell, and
  repeatedly swaps the new root with its smaller child;
- initialization repeatedly inserts decorated leaves.

The local operations are public rather than wrappers around Batteries'
private `maxChild`.  This keeps recursive equations available to Lean and lets
the proof expose the exact executed state.

`IsMinHeap` states that every in-range parent priority is no greater than each
in-range child priority.  The public heap state packages an array together
with this invariant; no sorted list is stored as executable ghost state.

## Proof decomposition

The development is split into focused modules:

- `HeapExecution/Entry.lean`: entries, priorities, stable decoration, and
  ordering facts;
- `HeapExecution/ArrayHeap.lean`: array invariant, child selection, bubbling,
  and raw executable operations;
- `HeapExecution/Operations.lean`: invariant preservation, length, multiset,
  and minimum-root specifications;
- `HeapExecution/Refinement.lean`: priority-sorted observation and exact
  simulation of `sortForest`/`insortTree`;
- `HeapExecution/Execution.lean`: total heap-Huffman loop and equality with
  `huffmanOfFreqs`;
- `HeapExecution/Cost.lean`: costed operations, erasure, logarithmic local
  bounds, and the total `O(n log n)` theorem;
- `HeapExecution.lean`: reader-facing facade and bundled correctness theorem.

This layout avoids adding more proof mass to the existing 3,000-line Huffman
file and permits compiling one proof layer at a time.

## Refinement theorem

For a valid heap, `orderedView` insertion-sorts its entries by lexicographic
priority.  Multiset preservation plus distinct priorities and root minimality
give the two central equations:

```lean
orderedView (insert h e) = insertEntry e (orderedView h)
orderedView h = e :: rest -> orderedView (extractMin h).heap = rest
```

The stamp discipline then proves that erasing `orderedView` after initialization
is `sortForest (leavesOfFreqs xs)`, and that one heap merge simulates one
`huffman` equation.  The final theorem is exact equality, not merely equality
of cost or frequencies:

```lean
heapHuffmanOfFreqs xs = huffmanOfFreqs xs
```

The existing `huffmanOfFreqs_correct` theorem can therefore supply frequency
preservation and optimality without duplicating the exchange argument.

## Cost model

Every executable loop returns both its value and the number of visited control
frames.  Array lookup, comparison, and swap are unit operations at this CLRS
abstraction level.  The erasure theorems show that removing the counter yields
the uncosted heap execution.

For a heap of size at most `n`, both upward and downward paths have at most
`Nat.log 2 n + 1` frames.  Repeated-insert initialization uses `n` operations;
each of the `n - 1` merges uses two extractions and one insertion.  A
conservative public bound is:

```lean
heapHuffmanWork xs <= (4 * xs.length + 1) * (Nat.log 2 xs.length + 1)
```

The theorem is attached to the returned execution record and replaces the
detached `textbookHeapHuffmanWork` envelope as the flagship complexity result.
The older list comparison theorem remains available and explicitly describes
the alternative list implementation.

## Acceptance and verification

The closure is accepted only when all of the following hold:

1. Native evaluation covers empty, singleton, tied-frequency, and ordinary
   multi-symbol inputs.
2. Focused tests check heap invariants, multiset behavior, exact refinement,
   optimality, and the total cost bound.
3. `Tests/Trust/Chapter_15.lean` audits the new flagship theorems and reports
   only the project's accepted foundational axioms.
4. The Chapter 15 facade imports the new public module, issue #338 records the
   verification evidence, and the proof-progress ledger is updated without
   overstating lower-level RAM or allocation costs.

## Scope boundary

The proof counts the comparisons and control frames of the textbook binary
heap algorithm.  It does not formalize machine words, allocator behavior,
cache effects, or imperative in-place mutation.  Those are not used to justify
the asymptotic theorem.
