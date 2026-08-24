# Chapter 34 Graph Well-Formedness Guard Plan

**Goal:** Reuse the existing CLIQUE target-bound, edge-order, and endpoint-
bound machines as one fixed polynomial-time Boolean guard for the shared graph
well-formedness predicate.

**Why this layer matters:** After syntax normalization, every stream has a
canonical graph parse.  The complement compiler must still reject target
overflow, reversed/self-loop edge records, and out-of-range endpoints before
enumerating complement pairs.  These conditions are already machine-checked
inside the CLIQUE verifier and should not be reimplemented.

**Boundary:** The guard consumes the established empty-certificate pair
encoding of a graph.  A later formatter will connect the ordinary graph stream
to that encoding, and a later branch will select either complement generation
or the direction-specific fallback.

## Task 1: Shared Boolean specification

- [x] Define the conjunction of target, edge-order, and endpoint-bound passes.
- [x] Prove exact equivalence with `CliqueInstance.WellFormed` on canonical
  graph encodings.

## Task 2: Concrete fixed machine

- [x] Combine the existing component TM2s with the reusable same-input Boolean
  AND construction.
- [x] Specialize the result to the empty-certificate graph-pair encoding.

## Task 3: Verification and checkpoint

- [x] Add a focused interface and axiom audit.
- [x] Build the focused test and Chapter 34 root, run repository consistency,
  and commit proof and documentation checkpoints separately.
