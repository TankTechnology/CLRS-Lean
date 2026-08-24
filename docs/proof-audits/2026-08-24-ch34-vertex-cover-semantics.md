# Chapter 34 VERTEX-COVER Semantic Checkpoint Audit

Date: 2026-08-24

## Accepted boundary

This checkpoint closes the typed textbook complement argument from general
CLIQUE to VERTEX-COVER.  It does not claim a polynomial-time reduction or
VERTEX-COVER NP-completeness.

The accepted Lean evidence is:

- `CliqueInstance.IsVertexCover` and `CliqueInstance.HasVertexCover`, using
  the standard at-most-target cover semantics;
- `vertexCoverNormalizedPairs` and
  `mem_vertexCoverNormalizedPairs_iff`, giving deterministic row-major
  enumeration of every normalized vertex pair;
- `vertexCoverComplementEdges` and
  `mem_vertexCoverComplementEdges_iff`, characterizing complement edges;
- `CliqueInstance.complementForVertexCover` and
  `CliqueInstance.complementForVertexCover_wellFormed`;
- `CliqueInstance.complement_hasVertexCover_of_hasClique`;
- `CliqueInstance.hasClique_of_complement_hasVertexCover`;
- the public assembly theorem
  `CliqueInstance.hasClique_iff_complement_hasVertexCover`.

The implementation is split across `Instance.lean`, `Complement.lean`,
`Soundness.lean`, `Completeness.lean`, and `ComplementSemantics.lean`.  The
split keeps the finite-set and graph arguments independently compilable and
avoids extending the already large Chapter 34 root proof file.

## Verification evidence

The following commands passed from a clean Chapter 34 worktree:

```bash
lake env lean Tests/Chapter_34_VertexCover_Semantics.lean
lake build CLRSLean.Chapter_34
python3 scripts/check_repository.py
git diff --check
```

The focused interface test checks the definitions, construction,
well-formedness theorem, and final equivalence.  Its axiom audit reports only:

```text
propext
Classical.choice
Quot.sound
```

The repository placeholder scan found no `sorry`, `admit`, or project axiom in
the new §34.5 source.  The Chapter 34 root build also caught and eliminated a
namespace collision with §34.4's occurrence-graph `normalizedPairs`; the
§34.5 internal construction now consistently uses the `vertexCover...`
prefix.

The progress ledger records Chapter 34 at 38/38 tracked theorems while
retaining one edition gap unit.  Section 34.5 is `partial`, specifically typed
semantic-only.

## Next missing bridge

The next acceptance target is the raw shared-encoding layer:

1. define the honest serialized `GeneralVERTEXCOVER` language;
2. define a canonical well-formed no-instance;
3. define a total `cliqueToVertexCoverMap` on every raw input;
4. prove exact all-input membership preservation.

After that, the map still needs a fixed polynomial-time machine and the target
needs a concrete verifier, NP membership, hardness transport, and the final
NP-completeness theorem.  HAM-CYCLE, TSP, and SUBSET-SUM remain later §34.5
work.  None of those statements is implied by this semantic checkpoint.

## Checkpoints

- `4cc12f79` — typed complement construction and semantic equivalence;
- `d929781c` — Chapter imports, navigation, progress ledgers, and repository
  integration.
