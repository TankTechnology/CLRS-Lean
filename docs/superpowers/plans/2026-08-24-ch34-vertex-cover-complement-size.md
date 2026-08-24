# Chapter 34 VERTEX-COVER Complement-Size Plan

**Goal:** Bound the deterministic complement construction and both total raw
semantic maps by an explicit polynomial in the source-string length.

**Why this layer matters:** The future fixed complement TM2 must enumerate at
most quadratically many pairs and emit at most cubically many unary symbols.
Publishing these bounds first isolates that mathematical obligation from the
machine simulation and gives its runtime proof a stable interface.

**Boundary:** This milestone proves representation-size bounds only.  It does
not yet claim that either raw map is computed by a fixed polynomial-time TM2.

## Task 1: Pair-enumeration bounds

- [x] Prove a linear length bound for each normalized-pair row.
- [x] Prove a quadratic length bound for the complete normalized-pair list and
  its filtered complement-edge list.

## Task 2: Complement-encoding bound

- [x] Bound every encoded complement edge by a linear function of the vertex
  count.
- [x] Prove a cubic bound for the encoded complemented instance.

## Task 3: Total raw-map bounds

- [x] Use successful-decoder field bounds to express the valid-input result in
  terms of the original raw input length.
- [x] Cover malformed and ill-formed fallbacks and publish bounds for both
  `cliqueToVertexCoverMap` and `vertexCoverToCliqueMap`.

## Task 4: Verification and checkpoint

- [x] Add a focused interface test for the new bounds.
- [x] Run the focused test, Chapter 34 root build, axiom audit, placeholder
  scan, and repository consistency checks.
- [x] Commit proof and public-ledger updates as separate checkpoints.
