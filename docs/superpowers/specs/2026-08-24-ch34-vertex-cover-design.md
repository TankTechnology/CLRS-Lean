# Chapter 34 VERTEX-COVER Design

## Goal

Formalize the textbook VERTEX-COVER decision problem as the first represented
problem in CLRS §34.5.  Reuse the honest graph-plus-`k` CLIQUE representation,
prove the complement reduction at the typed and raw-string levels, construct
the concrete polynomial-time reduction and verifier machines, and derive
VERTEX-COVER NP-completeness.

This subproject is complete only when the public serialized language has both
NP membership and NP-hardness.  Typed graph semantics, a polynomial output
bound, or a native Lean decision procedure are intermediate milestones.

## Accepted Route A

VERTEX-COVER reuses the existing `CliqueInstance` structure and `CliqueSym`
grammar because both decision problems consume exactly the same data:

```text
finite undirected graph + natural-number target
```

The language predicates differ, not the input grammar.  The target exposes
problem-facing aliases and wrappers:

```lean
abbrev VertexCoverInstance := CliqueInstance
abbrev VertexCoverSym := CliqueSym
abbrev encodeVertexCoverInstance := encodeCliqueInstance
abbrev decodeVertexCoverInstance := decodeCliqueInstance
abbrev encodeVertexCoverCertificate := encodeCliqueCertificate
abbrev decodeVertexCoverCertificate := decodeCliqueCertificate
```

This sharing is unambiguous: `CLIQUE` and `VERTEXCOVER` are separate `Language`
values over one graph-instance syntax, just as different decision predicates
may share a standard DIMACS-like grammar.

The implementation does not rename or refactor the already accepted CLIQUE
source.  A future neutral `GraphKInstance` migration is optional and outside
this subproject.

## Existing Reusable Boundary

The following §34.4 infrastructure is already available:

- `CliqueInstance` with `vertexCount`, `targetSize`, and normalized edge list;
- `CliqueInstance.WellFormed` and symmetric `CliqueInstance.Adj`;
- `CliqueInstance.HasClique` with exact target cardinality;
- complete instance and certificate encoders/parsers with round trips;
- encoding-length and canonicality results;
- a concrete parser, range checker, certificate normalizer, and polynomial-time
  machinery for general CLIQUE;
- `CLIQUE_npComplete` and hardness transport through the completed §34.4 chain.

Chapter 35 supplies useful mathematical intuition for vertex covers, but its
approximation-specific graph type is not used as the Chapter 34 decision
language.  Introducing a conversion to that type would add a second graph
representation without reducing the main proof burden.

## Closure Ledger at Entry

| Layer | Existing evidence | Status |
| --- | --- | --- |
| Source NP-completeness | `CLIQUE_npComplete` | closed |
| Shared graph-plus-`k` encoding | `CliqueInstance`, `CliqueSym`, parsers and round trips | closed |
| Typed vertex-cover semantics | no predicate on `CliqueInstance` | open |
| Typed complement equivalence | no clique/cover theorem | open |
| Raw target language | no `VERTEXCOVER` language | open |
| Total raw reduction | no complement map on strings | open |
| Serialized output size | no complement-encoding bound | open |
| Exact reduction machine | no fixed complement emitter | open |
| Target NP membership | no exact cover checker machine | open |
| Target NP-completeness | downstream of reduction and verifier | open |

The first missing bridge is the typed complement equivalence.  No machine work
begins before that theorem and its construction are stable.

## Typed Vertex-Cover Semantics

Definitions live in the existing `CLRS.Chapter34` namespace and extend
`CliqueInstance`:

```lean
def CliqueInstance.IsVertexCover
    (I : CliqueInstance) (vertices : Finset Nat) : Prop :=
  (∀ v ∈ vertices, v < I.vertexCount) ∧
    ∀ e ∈ I.edges, e.1 ∈ vertices ∨ e.2 ∈ vertices

def CliqueInstance.HasVertexCover (I : CliqueInstance) : Prop :=
  ∃ vertices : Finset Nat,
    vertices.card ≤ I.targetSize ∧ I.IsVertexCover vertices
```

The target uses the standard at-most-`k` decision predicate.  This differs
intentionally from `HasClique`, whose witness has exactly `targetSize`
vertices.

Repeated edge records remain harmless: covering every list member is
equivalent to covering every represented simple edge.  Vertex bounds are part
of the certificate semantics even though out-of-range vertices cannot help
cover a well-formed instance.

Public wrappers connect finite-set witnesses to duplicate-free list
certificates only after the finite-set truth source is proved.

## Deterministic Graph Complement

The complement must have a deterministic list order suitable for a later exact
machine theorem.  Define row-major normalized pairs using `List.range`:

```text
(0,1), (0,2), ..., (0,n-1),
       (1,2), ..., (1,n-1),
                    ...
```

`normalizedPairs n` lists every pair `(u,v)` exactly once with
`u < v < n`.  `complementEdges I` filters this list by normalized edge
nonmembership in `I.edges`.

The reduction instance is:

```lean
def CliqueInstance.complementForVertexCover (I : CliqueInstance) :
    CliqueInstance where
  vertexCount := I.vertexCount
  targetSize := I.vertexCount - I.targetSize
  edges := complementEdges I
```

Under `I.WellFormed`, this result is well formed.  The construction ignores
duplicates in the source edge list through membership, and its output edge list
is canonical and duplicate-free by the `normalizedPairs` theorem.

## Typed Reduction Theorem

The public semantic truth source is:

```lean
theorem CliqueInstance.hasClique_iff_complement_hasVertexCover
    (I : CliqueInstance) (hI : I.WellFormed) :
    I.HasClique ↔ I.complementForVertexCover.HasVertexCover
```

The forward direction takes a clique `S` and uses
`Finset.range I.vertexCount \ S`.  Its cardinality is exactly
`vertexCount - targetSize`.  A complement edge with neither endpoint in that
set would join two distinct members of the source clique and therefore would
have to be a source edge, contradicting complement membership.

The reverse direction takes a cover `C` of size at most
`vertexCount - targetSize`.  Its in-range complement has cardinality at least
`targetSize`.  `Finset.exists_subset_card_eq` selects an exact-size subset
`S`.  If two distinct members of `S` were not adjacent in the source graph,
their normalized pair would be a complement edge; the cover property would put
one endpoint in `C`, contradicting membership in `S`.

The proof is split into reusable helpers:

- membership and uniqueness of `normalizedPairs`;
- the exact `complementEdges` membership characterization;
- well-formedness of `complementForVertexCover`;
- in-range set-complement cardinality;
- clique-to-cover soundness;
- cover-to-clique completeness;
- the final `iff` wrapper.

## First Semantic Checkpoint

The initial implementation creates only:

```text
CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/
└── VertexCover/
    ├── Instance.lean
    ├── Complement.lean
    └── ComplementSemantics.lean

Tests/
└── Chapter_34_VertexCover_Semantics.lean
```

The interface test is written first with unresolved checks for:

```lean
#check CliqueInstance.HasVertexCover
#check CliqueInstance.complementForVertexCover
#check CliqueInstance.complementForVertexCover_wellFormed
#check CliqueInstance.hasClique_iff_complement_hasVertexCover
```

The focused test must fail for the missing names before source files are added.
The checkpoint is reported as typed `semantic-only`, not as a completed
polynomial-time reduction.

## Raw VERTEX-COVER Language

After typed semantics, define:

```lean
def GeneralVERTEXCOVER : Language VertexCoverSym :=
  { input |
      ∃ I,
        decodeVertexCoverInstance input = some I ∧
        I.WellFormed ∧ I.HasVertexCover }

abbrev VERTEXCOVER : Language VertexCoverSym := GeneralVERTEXCOVER
```

Malformed and decoded-but-ill-formed strings are no-instances.  The principal
raw theorem characterizes membership exactly, and canonical encodings receive
an `encode..._mem_..._iff` wrapper.

## Total Raw Reduction

The raw map decodes the source under the shared complete grammar:

```text
decode source
  ├─ well-formed I -> encode (I.complementForVertexCover)
  └─ otherwise     -> encode canonicalVertexCoverNoInstance
```

Use the well-formed two-vertex instance with target zero and edge `(0,1)` as
the canonical no-instance.  It has no cover of size at most zero.

The all-input theorem is:

```lean
cliqueToVertexCoverMap input ∈ VERTEXCOVER ↔ input ∈ CLIQUE
```

The valid branch uses the typed complement theorem.  Parser failure and
ill-formed branches reduce to the canonical no-instance lemma.

## Serialized Size and Reduction Machine

The complement contains at most `n * n` normalized pairs.  Under the unary
grammar, each endpoint and the target contribute at most a linear factor in
`n`, so a cubic bound in `input.length + 1` is sufficient.

The fixed machine reuses existing parsing, well-formedness, unary-counter,
nested-loop, membership-query, and instance-emission infrastructure.  Its new
semantic core enumerates row-major pairs and emits exactly those absent from the
source edge list.  It must compute the same `cliqueToVertexCoverMap` used by the
raw membership theorem.

Machine modules remain separate from semantic modules:

```text
VertexCover/Reduction/
├── Encoding.lean
├── EncodingBounds.lean
├── Machine.lean
├── MachineSemantics.lean
├── MachineRuntime.lean
└── Reduction.lean
```

The public reduction is packaged only after exact computation and the
original-input polynomial runtime are proved.

## Certificate Semantics and NP Membership

Reuse the existing list-of-unary-vertices certificate grammar.  A list
represents a cover when it is duplicate-free, has length at most the target,
contains only in-range vertices, and covers every stored edge.

The Boolean `vertexCoverVerifier` parses both strings and checks exactly those
conditions.  Its truth theorem quantifies over all raw strings.  From a
finite-set cover, the canonical `toList` certificate has at most
`vertexCount` records, and the existing unary certificate-length results lift
to a polynomial in instance length.

The concrete verifier can reuse CLIQUE syntax, canonicalization, range, and
duplicate checks, but it requires:

- an at-most-target cardinality pass instead of exact equality;
- an edge scan checking that at least one endpoint occurs in the certificate,
  instead of the CLIQUE all-pairs adjacency pass.

The accepted public results are:

```lean
generalVERTEXCOVER_polyTimeVerifiable :
  PolyTimeVerifiable GeneralVERTEXCOVER

generalVERTEXCOVER_mem_ClassNP :
  GeneralVERTEXCOVER ∈ ClassNP VertexCoverSym
```

## Hardness and NP-Completeness

Once the concrete reduction exists:

```lean
clique_reducible_to_vertexCover :
  PolyTimeReducible CLIQUE VERTEXCOVER

vertexCover_npHard : NPHard VERTEXCOVER

VERTEXCOVER_npComplete : NPComplete VERTEXCOVER
```

Hardness is transported from `CLIQUE_npComplete.2`; Cook--Levin is not
re-expanded.

## Full Module Boundary

The stable source tree is:

```text
Section_34_5_NP_Complete_Problems.lean
Section_34_5_NP_Complete_Problems/
├── VertexCover.lean
└── VertexCover/
    ├── Instance.lean
    ├── Complement.lean
    ├── ComplementSemantics.lean
    ├── Language.lean
    ├── Certificate.lean
    ├── CertificateLength.lean
    ├── VerifierMachine.lean
    ├── VerifierRuntime.lean
    ├── Reduction/
    │   ├── Encoding.lean
    │   ├── EncodingBounds.lean
    │   ├── Machine.lean
    │   ├── MachineSemantics.lean
    │   ├── MachineRuntime.lean
    │   └── Reduction.lean
    └── Completeness.lean
```

Large controllers may split further, but typed semantics, raw encoding,
machines, runtime, and public packaging do not collapse into one file.

## Verification and Commit Discipline

Each public layer follows RED-GREEN verification and receives its own commit:

1. typed cover semantics;
2. deterministic complement and typed reduction theorem;
3. raw language and certificate semantics;
4. total raw map and cubic output bound;
5. concrete reduction machine;
6. concrete verifier and NP membership;
7. hardness, NP-completeness, chapter wiring, and status updates.

Every checkpoint runs its narrow source build and interface test.  Final
acceptance additionally requires:

```text
lake build CLRSLean.Chapter_34
lake env lean Tests/Chapter_34_VertexCover_Interface.lean
python3 scripts/check_repository.py
placeholder scan
headline #print axioms audit
git diff --check
```

The edition map promotes §34.5 from `not-started` to `partial` when the first
typed theorem is publicly wired.  It does not report VERTEX-COVER complete
until the serialized language, concrete reduction, concrete verifier, and
`NPComplete` theorem all pass.

## Non-goals

- No neutral `GraphKInstance` refactor of existing CLIQUE sources.
- No duplicate VERTEX-COVER parser grammar.
- No HAM-CYCLE, TSP, or SUBSET-SUM implementation in this subproject.
- No reuse of Chapter 35 approximation theorems as decision-language proofs.
- No website rendering or deployment.
- No `sorry`, `admit`, project axiom, or completion claim based only on output
  size.
