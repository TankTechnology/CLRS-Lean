# Complexity Reduction Closure Skill Audit

Date: 2026-08-24

## Outcome

The repository now contains a local `complexity-reduction-closure` skill for
Lean polynomial-time reductions, NP membership, NP-hardness, and
NP-completeness.  It records the Chapter 34 proof discipline as a reusable
closure ledger rather than Cook--Levin-specific controller instructions.

The skill distinguishes five evidence levels:

- `semantic-only`;
- `size-certified`;
- `machine-certified`;
- `reduction-complete`;
- `np-complete`.

In particular, it rejects the inference from semantic correctness and
polynomial output length to polynomial-time computability.  A public reduction
requires a fixed machine computing the exact raw map and a runtime bound in the
original input length.

## Artifacts

- `.codex/skills/complexity-reduction-closure/SKILL.md` contains the trigger,
  closure loop, failure classification, and completion gate.
- Six focused references cover reduction packaging, NP membership,
  semantic-to-machine lifting, malformed input, polynomial bounds, and the
  Chapter 34 case study.
- `evals/evals.json` records CLIQUE-to-VERTEX-COVER, HAM-CYCLE gadget, and
  numeric SUBSET-SUM scenarios.
- Three dry runs demonstrate the common closure-ledger report surface.
- `scripts/test_complexity_reduction_closure_skill.py` validates the package
  contract and the route from `clrs-chapter-formalization`.

No global user skill or Codex configuration was modified.

## Red-Green Evidence

The initial package test ran before production skill files existed and failed
four tests for the missing entrypoint, references, evaluations, and dry runs.
After the core skill and references were added, only the three evaluation
layers remained failing.  Adding the approved evaluation fixtures made all
four tests pass.

The chapter-routing assertion was then added before modifying the existing
chapter skill.  It failed because `clrs-chapter-formalization` did not name the
new skill.  A five-line routing pattern made the complete five-test suite pass.

## Fresh Verification

The accepted package passed:

```text
python3 scripts/test_complexity_reduction_closure_skill.py
  Ran 5 tests: OK

python3 /home/ubuntu/.codex/skills/skill-creator/scripts/quick_validate.py \
  .codex/skills/complexity-reduction-closure
  Skill is valid!

python3 scripts/check_repository.py
  Repository checks passed.

git diff --check origin/main...HEAD
  no output
```

The repository check included edition-map, progress, status, book coverage,
source navigation, workflow policy, Lean placeholder, and Markdown local-link
checks.

## Commits

- `40977e2d`: approved skill design;
- `d246abe1`: executable implementation plan;
- `66eb14f7`: validated skill, references, evaluations, and package test;
- `18631329`: chapter-skill routing integration.

## First Live Use: VERTEX-COVER

The VERTEX-COVER dry run reuses the honest `CliqueInstance` graph-plus-`k`
model, its normalized edge representation, and the existing serialized grammar.
The first missing bridge is semantic, not machine-level:

```lean
I.WellFormed →
  I.HasClique ↔ (I.complementForVertexCover).HasVertexCover
```

The target cover predicate uses cardinality at most the target, while the
source clique predicate uses exact target size.  The complement construction
uses target `I.vertexCount - I.targetSize`.  The next design must expose the
set-complement cardinality and edge/nonedge incidence lemmas independently
before raw encoding or concrete machine work begins.

After typed semantics, the remaining ledger is:

1. define the honest serialized VERTEX-COVER language;
2. prove a total raw complement map and all-input membership equivalence;
3. bound complement serialization size;
4. prove a fixed polynomial-time machine computes that exact map;
5. add exact certificate semantics, certificate length, and a fixed checker;
6. transport NP-hardness from `CLIQUE_npComplete` and package VERTEX-COVER
   NP-completeness.

This is the accepted kickoff boundary for CLRS §34.5.
