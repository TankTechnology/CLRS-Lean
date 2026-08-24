# Complexity Reduction Closure Skill Design

## Goal

Create a repository-local Codex skill, `complexity-reduction-closure`, that
turns an informal or partially formalized complexity reduction into an honest,
kernel-checked Lean reduction with a precise completion boundary.

The skill captures the reusable proof strategy learned from Chapter 34.  It
must make the next missing proof bridge visible before implementation begins,
reuse established semantic and machine infrastructure, and prevent a
polynomial output-size theorem from being reported as a polynomial-time
reduction.

After the skill is accepted, it becomes the required workflow for the selected
Section 34.5 chain, beginning with VERTEX-COVER.

## Scope

The skill triggers for Lean work involving one or more of the following:

- `PolyTimeReducible` or an equivalent many-one reduction interface;
- NP membership, NP-hardness, or NP-completeness;
- a typed mathematical reduction that must be lifted to serialized languages;
- an exact raw map whose polynomial-time computation remains open;
- certificate semantics, certificate-size bounds, or concrete verifier
  machines;
- SAT, CLIQUE, VERTEX-COVER, HAM-CYCLE, TSP decision, SUBSET-SUM, or similar
  finite decision problems.

It is a proof-orchestration skill rather than a tactic cookbook.  General
statement shaping, invariant debugging, and abstraction conversion continue to
belong to `lean-proof-engineering` and `proof-bridge-strategy`.

## Non-goals

- Do not encode Cook--Levin-specific state names, wire indices, controller
  labels, or tableau formulas in the skill.
- Do not require a concrete machine when the requested theorem is explicitly
  semantic-only.  Instead, report the result as semantic-only and name the
  missing machine layer.
- Do not replace mathematical gadget reasoning with machine construction.
  Semantic soundness and completeness must stabilize first.
- Do not add a universal automation tactic or generate unreviewed Lean source.
- Do not treat Chapter 35 approximation models as already serialized Chapter
  34 decision languages.
- Do not change global user skills.  The first implementation is local to this
  repository under `.codex/skills/`.

## Relationship to Existing Skills

The new skill sits between three existing layers:

1. `clrs-chapter-formalization` decides which textbook claims count as the main
   chapter content and keeps coverage reporting honest.
2. `complexity-reduction-closure` determines the reduction-specific proof
   obligations, their order, and the exact missing bridge.
3. `lean-proof-engineering` and `proof-bridge-strategy` guide local theorem
   shaping, stuck-proof diagnosis, invariant lifting, and reusable conversions.

The Chapter formalization skill should eventually gain only a short routing
note to the new skill.  Its main file is already large and should not absorb
the detailed reduction workflow.

## Skill Package

The package has this shape:

```text
.codex/skills/complexity-reduction-closure/
├── SKILL.md
├── references/
│   ├── reduction-contract.md
│   ├── np-membership-contract.md
│   ├── semantic-to-machine.md
│   ├── encoding-and-malformed-input.md
│   ├── polynomial-bound-composition.md
│   └── ch34-case-study.md
└── evals/
    └── evals.json
```

`SKILL.md` contains the routing logic and closure loop.  Detailed checklists
and examples live in references so the main skill remains concise.  No bundled
script is included initially: theorem names and module layouts vary enough that
a name-based scanner would be brittle.  A deterministic audit script may be
added later only if repeated evaluations show the same mechanical inspection
being reimplemented.

## Core Reduction Contract

For a proposed map `f : List Γ₁ → List Γ₂` from language `A` to language `B`,
the skill constructs and maintains this ledger:

| Layer | Required evidence | Completion question |
| --- | --- | --- |
| Typed semantics | A mathematical construction and exact semantic theorem | Is the gadget/function mathematically correct in both directions? |
| Encoding | Encoder/parser contracts and a total raw map | Is `f` defined on every raw input string? |
| Malformed input | A canonical no-instance or proved total rejection policy | What happens on malformed or decoded-but-ill-formed input? |
| Raw semantics | `x ∈ A ↔ f x ∈ B` for every raw `x` | Does the theorem avoid a hidden well-formedness premise? |
| Output size | An explicit polynomial bound on `(f x).length` | Is the serialized output polynomially bounded? |
| Exact computation | A fixed machine computes exactly `f` | Is this the same map used by the semantic theorem? |
| Runtime | A polynomial step bound in the original input length | Is the machine polynomial in `x.length`, not an auxiliary script length? |
| Packaging | A public `PolyTimeReducible A B` theorem | Are semantics and computation joined at the public interface? |

The skill must distinguish the following statuses:

- `semantic-only`: typed or raw membership equivalence is proved;
- `size-certified`: semantic equivalence plus serialized output bound is proved;
- `machine-certified`: the exact raw map has a fixed polynomial-time machine;
- `reduction-complete`: the public polynomial-time reduction theorem is proved;
- `np-complete`: NP membership and NP-hardness are both proved for the honest
  serialized target language.

No earlier status may be described using a later status's wording.

## Proof Workflow

### 1. Inspect before designing

Read the source and target language definitions, encoders, parsers, certificate
interfaces, existing reductions, relevant interface tests, and progress docs.
Search for already proved bridge theorems before introducing new definitions.

The first user-facing work product is a compact closure ledger containing:

- the requested headline theorem;
- already closed layers;
- the first missing layer;
- the exact next theorem or representation decision;
- reusable modules and the narrow verification command.

### 2. Stabilize typed semantics

Define the mathematical instance transformation independently of raw parsing
and machine states.  Prove an exact `iff` whenever possible.  For gadget
reductions, split the proof into soundness and completeness, and first prove
local gadget lemmas that expose the correspondence used in both directions.

The typed semantic theorem is the truth source.  One-way wrappers are added
only when they remove repeated downstream proof friction.

### 3. Cross the encoding boundary

Reuse existing canonical encoders and parsers.  Prove round trips or locate
their existing theorems.  Define a total raw map with an explicit malformed
input policy.  Prefer a small, well-formed canonical no-instance when the
source parser rejects.

Then prove raw membership equivalence for all input strings.  The proof should
be a short bridge from parser cases to the typed semantic theorem; if it is not,
the encoding interface is probably missing a helper lemma.

### 4. Prove size before machine construction

Bound the number and magnitude of generated records before implementing the
concrete machine.  Separate structural counts from serialized symbol lengths.
For unary encodings, endpoint magnitudes contribute directly to output length;
for binary numeric encodings, prove bit-length bounds rather than numeric-value
bounds alone.

This step determines whether the intended raw map is suitable.  It does not by
itself establish polynomial-time computability.

### 5. Close the exact machine bridge

Construct a fixed machine only after the semantic map and output grammar are
stable.  Decompose it into phases with exact contracts:

```text
input suffix -> phase output ++ unchanged suffix
```

Each phase should expose:

- an exact run/output theorem;
- preservation of any stack, delimiter, or accumulator invariant;
- an exact or upper-bounded step count;
- an output-length fact needed by its caller.

Compose local bounds into a polynomial in the original raw input length.  A
bound in the length of a precomputed script is intermediate evidence only; the
script-generation cost and script-length bound must also be closed.

### 6. Package NP membership separately

For a target decision language, use the certificate triad:

1. exact Boolean checker semantics on raw certificate and instance strings;
2. existence of an accepted certificate with polynomial encoded length;
3. a fixed polynomial-time machine computing that exact checker.

Only then package `PolyTimeVerifiable` or membership in `ClassNP`.

### 7. Transport hardness instead of replaying it

Once `A` is NP-hard and `A ≤p B` is proved, use the repository's hardness
transport theorem.  Do not unfold Cook--Levin again.  NP-completeness is the
pair of the independently proved NP-membership and NP-hardness results.

### 8. Verify the public surface

Use interface-first development:

1. add the intended public `#check` and observe the missing-name failure;
2. implement the smallest theorem layer satisfying that interface;
3. run the narrow source and interface checks;
4. audit placeholders and headline theorem axioms;
5. update chapter guides, source navigation, edition map, proof map, progress
   CSV, and generated progress dashboard when coverage changes;
6. run the Chapter root and repository gates before a completion claim.

Large proofs are split into small files by semantic responsibility so a local
edit does not force repeated compilation of one monolithic file.

## Failure Triage

When progress stalls, classify the blocker before changing tactics:

- `statement`: the public theorem is weaker or stronger than downstream use;
- `semantic`: a gadget correspondence or certificate direction is missing;
- `representation`: typed and raw models lack a round-trip or membership bridge;
- `totality`: malformed input behavior is unspecified;
- `size`: record count or numeric encoding length is not bounded;
- `machine`: no fixed program computes the exact semantic map;
- `runtime`: the current bound depends on generated data rather than raw input;
- `packaging`: all ingredients exist but no public reduction/NP theorem joins
  them;
- `surface`: the theorem compiles but is not imported, tested, or documented.

The skill selects one class and one next theorem.  It must not respond to a
representation blocker by repeatedly trying unrelated tactics.

## Section 34.5 Bootstrap

After the skill is implemented, the first live use is VERTEX-COVER:

1. reuse `GeneralClique.CliqueInstance` and its honest graph encoding;
2. inspect the Chapter 35 `IsVertexCoverOn` mathematics for reusable semantic
   lemmas without importing approximation-specific claims as decision-language
   results;
3. specify an honest serialized graph-plus-`k` VERTEX-COVER language;
4. prove the typed complement equivalence between a clique of size `k` and a
   vertex cover of size `|V| - k`;
5. lift it to a total raw map, output bound, fixed polynomial-time machine, and
   public reduction;
6. add an exact certificate checker and prove VERTEX-COVER NP-complete.

HAM-CYCLE, TSP decision, and SUBSET-SUM receive separate design and
implementation plans after this first application validates the skill.  Their
mathematical layers may reuse Chapter 35 tour and subset-sum concepts, but each
still needs an honest Chapter 34 serialized decision-language interface.

## Evaluations

The first skill draft is checked against three repository-grounded prompts:

1. **CLIQUE to VERTEX-COVER:** the response must reuse the honest clique graph,
   identify complement/parameter arithmetic, require total raw semantics, and
   not stop at the typed graph equivalence.
2. **HAM-CYCLE gadget reduction:** the response must put local gadget
   soundness/completeness before encoding and machine work, and must split the
   large proof into focused modules.
3. **SUBSET-SUM numeric reduction:** the response must distinguish numeric
   magnitude from serialized bit length and include malformed-input and
   arithmetic-runtime obligations.

Each evaluation checks that the skill produces a complete obligation ledger,
identifies exactly one first missing bridge, proposes focused file boundaries,
and avoids claiming `PolyTimeReducible` from semantic correctness plus output
size alone.

Because the active agent policy does not authorize delegated evaluation runs,
the initial validation is performed inline against these three prompts.  A
future explicitly authorized benchmark may compare with-skill and baseline
runs using the skill-creator evaluation harness.

## Acceptance Criteria

The skill is accepted when all of the following hold:

- its description triggers on concrete complexity-reduction proof work but not
  on unrelated local Lean lemmas;
- `SKILL.md` routes to each reference at the correct proof stage;
- the contract distinguishes semantic, size, machine, reduction, and
  NP-completeness closure;
- the three evaluation prompts and expected outcomes are recorded in valid
  `evals/evals.json`;
- a dry run on the current VERTEX-COVER boundary produces the intended first
  theorem and module plan;
- repository checks and `git diff --check` pass;
- the skill introduces no changes to global user configuration.

## Commit Boundary

The design specification is committed independently.  After review, the skill
package, its evaluations, the VERTEX-COVER design, and each proof milestone are
separate commits.  This preserves the user's requirement that progress remain
independently reviewable and bisectable.
