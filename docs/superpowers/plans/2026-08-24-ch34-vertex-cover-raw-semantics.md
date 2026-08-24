# Chapter 34 VERTEX-COVER Raw Semantics Plan

**Goal:** Lift the accepted typed CLIQUE-to-VERTEX-COVER theorem through the
shared graph-plus-target encoding and prove exact membership preservation for a
total raw-string map.

**Boundary:** This milestone proves an all-input semantic map only.  It does
not claim that the map is computed by a fixed polynomial-time TM2, that
VERTEX-COVER is in NP, or that it is NP-complete.

## Task 1: Public RED interface

- [x] Add `Tests/Chapter_34_VertexCover_RawSemantics.lean` checking the raw
  language, canonical no-instance, total map, and all-input equivalence.
- [x] Run the test and confirm the new language module is missing.

## Task 2: Honest raw VERTEX-COVER language

- [x] Add `VertexCover/Language.lean` defining `GeneralVERTEXCOVER` over the
  shared `CliqueSym` grammar.
- [x] Prove exact raw membership, canonical-encoding membership, and parser
  rejection theorems.
- [x] Export `VERTEXCOVER` as the public language alias.

## Task 3: Total semantic reduction

- [x] Add `VertexCover/RawReduction.lean`.
- [x] Define a well-formed two-vertex, target-zero canonical no-instance and
  prove it is outside VERTEX-COVER.
- [x] Define `cliqueToVertexCoverMap`: decode and check well-formedness, emit
  the typed complement on the valid branch, and emit the canonical no-instance
  otherwise.
- [x] Prove `cliqueToVertexCoverMap input ∈ VERTEXCOVER ↔ input ∈ CLIQUE`
  for every raw input, including malformed and decoded-but-ill-formed strings.

## Task 4: Verification and checkpoint

- [x] Make the public interface test GREEN and audit headline axioms.
- [x] Scan the new modules for proof placeholders.
- [x] Build the focused facade and Chapter 34 root.
- [x] Run `scripts/check_repository.py` and `git diff --check`.
- [x] Commit the raw semantic checkpoint separately from later machine work.
