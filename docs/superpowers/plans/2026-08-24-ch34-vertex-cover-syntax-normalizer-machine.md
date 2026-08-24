# Chapter 34 Graph Syntax-Normalizer Machine Plan

**Goal:** Build a fixed linear-time TM2 that preserves every syntactically
valid graph-instance encoding and maps parser failures to one syntactically
valid but deliberately ill-formed graph sentinel.

**Why the sentinel matters:** The existing CLIQUE canonicalizer defaults
parser failures to the empty graph, which is well formed and can be a
yes-instance.  A complement reduction must retain rejection information until
the shared well-formedness guard selects its direction-specific no-instance.
The sentinel `{ vertexCount := 0, targetSize := 1, edges := [] }` is canonical
syntax but violates `targetSize ≤ vertexCount`.

**Boundary:** This machine closes raw parser normalization only.  It does not
yet validate all graph invariants or emit complement edges.

## Task 1: Pure contract and controller

- [x] Define the malformed-graph sentinel and prove it is not well formed.
- [x] Define the syntax-normalized value and byte stream.
- [x] Implement a fixed parser/buffer/restore/fallback controller.

## Task 2: Local simulations

- [x] Prove scan, restore, clear, and sentinel-emission runs independently.
- [x] Assemble the exact all-input run theorem.

## Task 3: Semantic and runtime closure

- [x] Prove the emitted stream is exactly the canonical encoding of the
  syntax-normalized value.
- [x] Package a fixed linear-time `TM2ComputableInPolyTime` witness.

## Task 4: Verification and checkpoint

- [x] Add a focused regression interface and axiom audit.
- [x] Build the new modules and Chapter 34 root; run placeholder and repository
  consistency checks.
- [x] Commit proof and public-ledger updates as separate checkpoints.
