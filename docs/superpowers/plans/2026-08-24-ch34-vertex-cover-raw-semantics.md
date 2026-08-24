# Chapter 34 VERTEX-COVER Raw Semantics Plan

**Goal:** Lift the accepted typed CLIQUE-to-VERTEX-COVER theorem through the
shared graph-plus-target encoding and prove exact membership preservation for a
total raw-string map.

**Boundary:** This milestone proves an all-input semantic map only.  It does
not claim that the map is computed by a fixed polynomial-time TM2, that
VERTEX-COVER is in NP, or that it is NP-complete.

## Task 1: Public RED interface

- [ ] Add `Tests/Chapter_34_VertexCover_RawSemantics.lean` checking the raw
  language, canonical no-instance, total map, and all-input equivalence.
- [ ] Run the test and confirm the new language module is missing.

## Task 2: Honest raw VERTEX-COVER language

- [ ] Add `VertexCover/Language.lean` defining `GeneralVERTEXCOVER` over the
  shared `CliqueSym` grammar.
- [ ] Prove exact raw membership, canonical-encoding membership, and parser
  rejection theorems.
- [ ] Export `VERTEXCOVER` as the public language alias.

## Task 3: Total semantic reduction

- [ ] Add `VertexCover/RawReduction.lean`.
- [ ] Define a well-formed two-vertex, target-zero canonical no-instance and
  prove it is outside VERTEX-COVER.
- [ ] Define `cliqueToVertexCoverMap`: decode and check well-formedness, emit
  the typed complement on the valid branch, and emit the canonical no-instance
  otherwise.
- [ ] Prove `cliqueToVertexCoverMap input ∈ VERTEXCOVER ↔ input ∈ CLIQUE`
  for every raw input, including malformed and decoded-but-ill-formed strings.

## Task 4: Verification and checkpoint

- [ ] Make the public interface test GREEN and audit headline axioms.
- [ ] Scan the new modules for proof placeholders.
- [ ] Build the focused facade and Chapter 34 root.
- [ ] Run `scripts/check_repository.py` and `git diff --check`.
- [ ] Commit the raw semantic checkpoint separately from later machine work.
