---
name: complexity-reduction-closure
description: Use for Lean formalization of polynomial-time many-one reductions, NP membership, NP-hardness, or NP-completeness, especially when bridging typed semantics to serialized raw languages, certificate checkers, concrete machines, and polynomial runtime bounds. Trigger for SAT, CLIQUE, VERTEX-COVER, HAM-CYCLE, TSP decision, SUBSET-SUM, PolyTimeReducible, ClassNP, NPHard, or when a reduction is semantically proved but not yet honestly closed.
---

# Complexity Reduction Closure

Turn a partially formalized complexity reduction into the strongest honestly
supported public theorem.  Treat reduction work as a sequence of explicit
proof layers.  Find the first missing bridge before writing more code.

The recurring failure to prevent is this invalid inference:

```text
semantic correctness + polynomial output length
  therefore polynomial-time computability
```

Output size and computation time are separate obligations.  A completed Lean
many-one reduction needs a fixed machine computing the exact map used by the
semantic theorem, with a polynomial runtime bound in the original input
length.

## Coordinate with Other Skills

- Use `clrs-chapter-formalization` to decide textbook scope and honest chapter
  status.
- Use `lean-proof-engineering` for statement shaping, local proof debugging,
  arithmetic isolation, and public theorem wrappers.
- Use `proof-bridge-strategy` when two mature formalized representations need a
  reusable conversion.

This skill owns the reduction-specific order of proof obligations.

## Required First Pass

Inspect the repository before designing:

1. Read the source and target language definitions.
2. Locate encoders, parsers, well-formedness predicates, and round trips.
3. Locate typed semantic theorems and raw membership theorems.
4. Locate certificate checkers and certificate-size results.
5. Locate concrete machine interfaces and polynomial composition helpers.
6. Read interface tests, imports, progress ledgers, and recent proof audits.

Then emit a closure ledger before implementation:

```markdown
## Closure ledger

| Layer | Current evidence | Status |
| --- | --- | --- |
| Typed semantics | ... | closed/open |
| Encoding and totality | ... | closed/open |
| Raw membership iff | ... | closed/open |
| Serialized output size | ... | closed/open |
| Exact machine computation | ... | closed/open |
| Original-input runtime | ... | closed/open |
| Reduction packaging | ... | closed/open |
| Target NP membership | ... | closed/open/not requested |

## First missing bridge

One exact theorem or one representation decision.

## File decomposition

Small modules in dependency order.

## Narrow verification

The command that checks the first milestone.
```

Select exactly one first missing bridge.  Do not answer a representation gap
by trying unrelated tactics or starting a downstream machine.

## Closure Status Vocabulary

Use these labels precisely:

- `semantic-only`: typed or raw semantic equivalence is proved, but no claim of
  polynomial-time computation is made.
- `size-certified`: semantic equivalence and serialized output-size bounds are
  proved.
- `machine-certified`: a fixed machine computes the exact raw map in polynomial
  time, but the public reduction wrapper may remain.
- `reduction-complete`: the public polynomial-time many-one reduction theorem
  is proved.
- `np-complete`: the honest serialized target has both NP membership and
  NP-hardness.

Never describe an earlier status using a later status's wording.

Read [references/reduction-contract.md](references/reduction-contract.md) when
shaping the ledger, semantic truth source, public reduction theorem, or
hardness packaging.

## Closure Loop

Follow this order unless inspection proves a stage is already closed:

```text
inspect local interfaces
  -> emit closure ledger
  -> select one first missing bridge
  -> stabilize typed semantic iff
  -> totalize raw encoding
  -> prove all-input raw membership iff
  -> prove serialized output size
  -> compute the exact same map with a fixed machine
  -> lift runtime to original input length
  -> package reduction / NP membership / hardness
  -> verify public surface and status honesty
```

### Stabilize Mathematical Semantics

Define the typed instance transformation independently of parsers and machine
states.  Prefer one exact `iff` as the truth source.  For gadget reductions,
prove local gadget correspondence first, then prove global soundness and
completeness separately.

Do not weaken the semantic theorem merely to fit the current encoding.  Add a
small bridge theorem or revise the representation if the intended textbook
claim is obscured.

### Cross the Raw Encoding Boundary

Reuse canonical encoders and parsers.  Separate parser success from instance
well-formedness.  Make the raw map total and give malformed or decoded-but-
ill-formed input an explicit result, usually a small canonical no-instance.

Prove membership equivalence for every raw input string, without a hidden
well-formedness premise.

Read
[references/encoding-and-malformed-input.md](references/encoding-and-malformed-input.md)
for the exact checklist and proof shapes.

### Prove Serialized Size

Bound generated record counts and encoded field lengths separately.  Unary
encodings charge numeric magnitude directly; binary encodings require bit-
length bounds.  State an explicit polynomial over raw input length.

Read
[references/polynomial-bound-composition.md](references/polynomial-bound-composition.md)
for structural-to-serialized bounds and local-to-global polynomial lifting.

### Close the Exact Machine Bridge

Construct a fixed machine only after the semantic map and output grammar are
stable.  Decompose long machines into phases with contracts of the form:

```text
input suffix -> phase output ++ unchanged suffix
```

For every phase prove exact output, invariant preservation, a step bound, and
the output-length fact needed by its caller.  A bound in the length of a
precomputed script is intermediate only: also compute that script and bound its
length by the original input.

Read [references/semantic-to-machine.md](references/semantic-to-machine.md)
before implementing or composing concrete machines.

### Package NP Membership Independently

Use the certificate triad:

1. exact Boolean checker semantics on raw certificate and instance strings;
2. an accepted certificate with polynomial encoded length;
3. a fixed polynomial-time machine computing that exact checker.

Read
[references/np-membership-contract.md](references/np-membership-contract.md)
when the target language must be shown to lie in NP.

### Transport Hardness

Once an NP-hard language reduces to the target, use the repository's hardness
transport theorem.  Do not replay Cook--Levin.  Construct NP-completeness only
from independently verified NP membership and NP-hardness.

Read [references/ch34-case-study.md](references/ch34-case-study.md) for the
Chapter 34 examples, reusable interfaces, and rejected shortcuts that motivated
this workflow.

## Interface-First Proof Development

For every public milestone:

1. Add the intended `#check` to a focused interface test.
2. Run the test and confirm the expected missing-name failure.
3. Implement the smallest semantic or machine layer that satisfies it.
4. Build the narrow source module and rerun the interface test.
5. Keep definitions, semantics, encoding, machines, runtime, and public
   packaging in separate focused files when any one layer becomes large.
6. Commit independently reviewable milestones.

Do not add `sorry`, `admit`, or project axioms to imported proof sources.

## Failure Classification

Classify a stuck reduction as exactly one of:

- `statement`: the theorem shape mismatches downstream use;
- `semantic`: a gadget or certificate direction is missing;
- `representation`: typed and raw models lack a bridge;
- `totality`: malformed-input behavior is unspecified;
- `size`: structural or numeric encoding bounds are missing;
- `machine`: no fixed program computes the exact semantic map;
- `runtime`: the bound depends on auxiliary generated data;
- `packaging`: ingredients exist but no public theorem joins them;
- `surface`: the theorem is not imported, tested, or documented.

State the classification and the exact next theorem before proceeding.

## Completion Gate

Before reporting a reduction or NP-completeness result complete:

1. Re-read the closure ledger and attach evidence to every claimed closed row.
2. Run the focused interface test and source build.
3. Run the chapter root build and repository policy checks.
4. Scan for unfinished proof markers.
5. Audit axioms of headline theorems.
6. Run `git diff --check`.
7. Synchronize chapter guides, source navigation, edition map, proof map,
   progress CSV, and generated dashboard when public coverage changes.

Report any remaining row by its exact missing theorem or representation layer,
not by saying only that it is difficult.
