# Chapter 34 VERTEX-COVER Certificate Semantics Plan

**Goal:** Give the honest raw VERTEX-COVER language an executable Boolean
certificate checker, prove its exact typed/raw semantics, and prove a uniform
polynomial certificate-length bound.

**Reuse:** Keep the shared graph-plus-target parser and the existing unary
list-of-vertices certificate codec.  Reuse the already proved certificate
encoding-length lemmas from general CLIQUE; introduce only the
VERTEX-COVER-specific predicate that every stored edge meets the selected
vertex list.

**Boundary:** This checkpoint closes function-level certificate semantics.  It
does not yet claim `VERTEXCOVER ∈ NP`: that requires a fixed polynomial-time
TM2 computing the checker Boolean on paired certificate/input strings.

## Task 1: Public RED interface

- [x] Add `Tests/Chapter_34_VertexCover_Certificate.lean` checking the list
  predicate, Boolean verifier, exact truth theorem, typed witness equivalence,
  and bounded-certificate language theorem.
- [x] Run the test and confirm the certificate module is missing.

## Task 2: Typed checker predicate

- [x] Add `VertexCover/Certificate/Basic.lean`.
- [x] Define `ListRepresentsVertexCover` using a duplicate-free in-range list
  of length at most the target that covers every stored edge.
- [x] Define the total raw Boolean `vertexCoverVerifier` over the shared
  instance and certificate parsers.

## Task 3: Exact semantics

- [x] Add `VertexCover/Certificate/Semantics.lean`.
- [x] Characterize `vertexCoverVerifier = true` for every raw certificate and
  input, including parser failures.
- [x] Prove `HasVertexCover ↔ ∃ vertices, ListRepresentsVertexCover vertices`.

## Task 4: Polynomial certificate length

- [x] Add `VertexCover/Certificate/Length.lean` and reuse the general-CLIQUE
  unary certificate length lemmas.
- [x] Prove every member has an accepted certificate of length at most
  `(input.length + 1)^2`.
- [x] Prove the exact bounded-certificate characterization of
  `GeneralVERTEXCOVER`.

## Task 5: Verification and checkpoint

- [x] Make the public interface test GREEN and audit headline axioms.
- [x] Scan the new modules for proof placeholders.
- [x] Build the focused facade and Chapter 34 root.
- [x] Run `scripts/check_repository.py` and `git diff --check` after wiring.
- [x] Commit proof and documentation checkpoints separately from the concrete
  machine layer.
