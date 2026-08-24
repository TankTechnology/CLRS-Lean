# Chapter 34 VERTEX-COVER Reverse Semantic Reduction Plan

**Goal:** Prove that the deterministic complement construction also reduces
VERTEX-COVER back to general CLIQUE, first for typed well-formed instances and
then for every raw string.

**Why this bridge matters:** A single future fixed polynomial-time complement
machine can then be reused in both directions: it transports CLIQUE hardness to
VERTEX-COVER and allows the existing concrete CLIQUE verifier to serve as the
machine backend for VERTEX-COVER NP membership.

**Boundary:** This milestone proves total semantic maps in both directions.  It
does not yet claim polynomial-time computability of the complement map.

## Task 1: Typed forward direction

- [x] Add a focused public test for the typed reverse equivalence and raw map.
- [x] Prove that a cover of size at most `k` leaves at least `|V|-k` vertices,
  from which an exact-size clique can be chosen in the complement graph.

## Task 2: Typed reverse direction

- [x] Prove that the complement of an exact `|V|-k` clique covers every source
  edge and has size at most `k`.
- [x] Package the exact well-formed equivalence
  `HasVertexCover ↔ complementForVertexCover.HasClique`.

## Task 3: Total raw map

- [x] Reuse the existing well-formed `noCliqueInstance` as the malformed and
  ill-formed fallback.
- [x] Define `vertexCoverToCliqueMap` and prove exact membership preservation
  for every raw input.

## Task 4: Verification and checkpoint

- [x] Run the focused test and headline axiom audit.
- [x] Scan for proof placeholders and run `git diff --check`.
- [x] Commit the typed/raw reverse bridge separately from later machine work.
