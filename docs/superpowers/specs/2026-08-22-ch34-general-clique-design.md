# Chapter 34 General CLIQUE Design

## Goal

Replace the misleading compatibility use of `CLIQUE` with an honest serialized
general graph-plus-`k` decision language.  Preserve the existing specialized
3-CNF occurrence language under an explicit name, prove the textbook
3-CNF-to-CLIQUE bridge, and give the general language an exact certificate
semantics and a concrete polynomial-time verifier.

This is the first remaining Chapter 34 textbook subproject.  VERTEX-COVER is a
separate follow-up design after the public CLIQUE interface is stable.

## Existing boundary

The current declaration

```lean
abbrev CLIQUE : Language GraphSym := ThreeCNFOccurrenceCLIQUE
```

does not encode an arbitrary graph or an explicit target size.  Its alphabet is
a relabeled CNF alphabet, and its graph and target size are reconstructed from
the decoded CNF.  The semantic theorem
`cnfSatisfiable_iff_hasClique` and the concrete reduction to
`ThreeCNFOccurrenceCLIQUE` remain useful and are not deleted.

The old branch `codex/ch34-textbook-closure` contains no unmerged general
CLIQUE implementation.  The new work therefore starts from `origin/main` and
does not import speculative code from that branch.

## Rejected alternatives

### Overload `GraphSym` with a second grammar

A parser could distinguish a legacy relabeled-CNF form from an explicit graph
form.  This would reuse the old machine alphabet, but one language would then
have two unrelated representations and the meaning of a string would depend on
format-dispatch rules.  That conflicts with the requirement that the public
language be unambiguous.

### Prove only a typed `SimpleGraph` theorem

A theorem over `SimpleGraph (Fin n)` would give clean mathematics but would not
define a language of finite strings, a certificate format, or a
polynomial-time reduction.  It is useful as an internal semantic view, not as
the Chapter 34 decision problem.

## Canonical instance model

The mathematical instance is:

```lean
structure CliqueInstance where
  vertexCount : Nat
  targetSize : Nat
  edges : List (Nat × Nat)
```

`CliqueInstance.WellFormed I` means all of the following:

- `I.targetSize ≤ I.vertexCount`;
- `I.edges.Nodup`;
- every `(u, v) ∈ I.edges` satisfies `u < v` and
  `v < I.vertexCount`.

Thus every undirected edge has exactly one stored orientation, self-loops are
absent, endpoints are in range, and duplicate edges are absent.

`CliqueInstance.Adj I u v` is symmetric: for `u < v` it checks `(u, v)` and for
`v < u` it checks `(v, u)`.  It is false when `u = v`.

`CliqueInstance.HasClique I` means that there is a `Finset Nat` whose cardinality
is exactly `I.targetSize`, whose vertices are all below `I.vertexCount`, and
whose distinct members are pairwise adjacent.  The principal semantic API is
an exact `iff`, with membership, bound, cardinality, and adjacency projections
added only when they remove repeated downstream proof work.

## Unique serialized grammar

The finite alphabet `CliqueSym` contains distinct structural constructors:

```text
instanceMark     certificateMark
tick             fieldSep
edgeMark         vertexMark
pairSep          recordEnd
```

Natural numbers use unary `tick` runs.  A graph instance has exactly this
grammar:

```text
instanceMark
tick^vertexCount fieldSep
tick^targetSize  fieldSep
(edgeMark tick^u pairSep tick^v recordEnd)*
```

A certificate has exactly this grammar:

```text
certificateMark
(vertexMark tick^v recordEnd)*
```

The parsers consume the complete list.  A missing marker, misplaced marker,
trailing fragment, or token from the other grammar returns `none`.  There is no
fallback parser and no legacy-format branch.

`encodeCliqueInstance` and `decodeCliqueInstance` satisfy an unconditional
round trip on the structure.  Well-formedness is checked separately by the
language.  `encodeCliqueCertificate` and `decodeCliqueCertificate` satisfy the
corresponding list round trip.

The raw general language is:

```lean
def GeneralCLIQUE : Language CliqueSym :=
  { input |
      ∃ I, decodeCliqueInstance input = some I ∧
        I.WellFormed ∧ I.HasClique }
```

Consequently malformed and decoded-but-ill-formed inputs are no-instances.

## Certificate semantics and NP membership

`cliqueVerifier certificate input` performs these checks:

1. both strings parse under their distinct complete grammars;
2. the graph instance is well formed;
3. the certificate vertex list is duplicate-free;
4. its length equals the target size;
5. every selected vertex is in range;
6. every pair of different selected vertices is adjacent.

The checker is Boolean and total.  Its truth theorem is exact on all raw
strings:

```lean
cliqueVerifier certificate input = true
  ↔ ∃ I vertices,
      decodeCliqueInstance input = some I ∧
      decodeCliqueCertificate certificate = some vertices ∧
      I.WellFormed ∧
      vertices represent a clique of size I.targetSize
```

Existence of an accepted certificate is then equivalent to
`input ∈ GeneralCLIQUE`.  A canonical increasing certificate obtained from a
clique has length at most `(input.length + 1)^2`; this supplies the certificate
polynomial.

The concrete verifier machine must compute this exact Boolean checker, not a
different mathematical predicate.  It is split into parsing, vertex checks,
pair checks, and runtime assembly modules.  The runtime theorem publishes a
named explicit `Polynomial Nat` bound derived from the machine proof.  Once
assembled, the public results are:

```lean
generalCLIQUE_polyTimeVerifiable : PolyTimeVerifiable GeneralCLIQUE
generalCLIQUE_mem_ClassNP : GeneralCLIQUE ∈ ClassNP CliqueSym
```

## Textbook occurrence-graph reduction

For a decoded CNF `f`, vertices are literal **positions**, enumerated in
row-major clause/position order.  This preserves repeated literal occurrences
as distinct graph vertices, exactly as in the textbook construction.

For two distinct numeric vertex indices, the generated edge is present exactly
when the indexed occurrences belong to different clauses and their literals are
not complementary.  Generated edges are normalized to `u < v`, listed without
duplicates, and all endpoints are below the number of literal occurrences.
The target size is `f.length`.

The project's `IsThreeCNF` predicate uses the at-most-three convention and
therefore permits empty clauses.  Consequently, structural well-formedness of
the literal-position instance uses the exact hypothesis that every clause is
nonempty, not merely `IsThreeCNF f`.  A satisfying assignment supplies this
hypothesis automatically.  If a 3-CNF contains an empty clause, it is
unsatisfiable and its occurrence instance is rejected, as required.

The semantic bridge reuses the existing assignment/clique argument through an
explicit equivalence between selected numeric positions and valid occurrence
vertices.  Its headline theorem is:

```lean
cnfSatisfiable_iff_occurrenceCliqueInstance (f : CNF) :
  CnfSatisfiable f ↔ (occurrenceCliqueInstance f).HasClique
```

The total raw reduction is:

```text
decode source CNF
  ├─ if it is an at-most-three-literal CNF: encode its occurrence instance
  └─ otherwise: encode a well-formed canonical no-instance
       (two vertices, target two, and no edge)
```

It proves, for every raw source string:

```lean
threeCNFToGeneralCliqueMap x ∈ GeneralCLIQUE ↔ x ∈ ThreeCNFSat
```

The number of occurrence vertices is at most the source length.  The explicit
edge list contains at most the square of that number, and unary endpoints add
one further factor.  The serialized output target is therefore

```lean
(threeCNFToGeneralCliqueMap x).length ≤ 64 * (x.length + 1)^3.
```

The concrete reduction machine computes `threeCNFToGeneralCliqueMap` exactly
and exposes a named polynomial runtime theorem.  It may reuse the verified
bounded scan and nested-loop infrastructure, but its public result must target
the new `CliqueSym` alphabet:

```lean
threeCNFSat_reducible_to_generalCLIQUE :
  PolyTimeReducible ThreeCNFSat GeneralCLIQUE
```

## Public-name migration

Migration is atomic at the final interface checkpoint:

- `ThreeCNFOccurrenceCLIQUE` keeps its existing name and alphabet;
- the old concrete theorem
  `threeCNFSat_reducible_to_threeCNFOccurrenceCLIQUE` remains available;
- `GeneralCLIQUE` keeps the descriptive implementation name;
- `CLIQUE` becomes an alias of `GeneralCLIQUE`, over `CliqueSym`;
- `threeCNFSat_reducible_to_CLIQUE` is restated against the new honest target;
- no declaration describes the specialized occurrence language simply as
  `CLIQUE` after migration.

The alias is not switched while only semantic scaffolding exists.  It is
switched only after the general encoding, raw reduction theorem, concrete
reduction, verifier semantics, and `GeneralCLIQUE ∈ NP` all pass their public
interface tests.

## Module boundaries

The implementation uses focused modules under
`Section_34_4_NP_Completeness_Proofs/GeneralClique/`:

- `Instance.lean`: instance, well-formedness, adjacency, and clique semantics;
- `Encoding.lean`: `CliqueSym`, exact parsers/encoders, and round trips;
- `Language.lean`: `GeneralCLIQUE` and raw membership characterizations;
- `Certificate.lean`: certificate representation, Boolean checker, and exact
  semantic theorem;
- `VerifierMachine/Core.lean`: concrete checker machine;
- `VerifierMachine/Semantics.lean`: exact output theorem;
- `VerifierMachine/PolynomialRuntime.lean`: explicit uniform runtime bound;
- `NP.lean`: `PolyTimeVerifiable` and `ClassNP` assembly;
- `OccurrenceReduction/Instance.lean`: indexed occurrence graph construction;
- `OccurrenceReduction/Semantics.lean`: satisfiability/clique equivalence;
- `OccurrenceReduction/Encoding.lean`: total raw map and cubic length bound;
- `OccurrenceReduction/Machine.lean`: exact polynomial-time reduction machine;
- `Public.lean`: final `CLIQUE` name migration and textbook-facing theorems;
- `GeneralClique.lean`: ordered facade importing the stable public stack.

Large controller or arithmetic proofs may be split further, but unrelated
definitions are not moved out of existing files.

## Test and commit discipline

`Tests/Chapter_34_GeneralClique_Interface.lean` is written first.  Each public
name is added as a failing `#check`, and the narrow test must fail because that
name does not yet exist before production code is added.

Acceptance checkpoints are committed separately:

1. approved design and implementation plan;
2. instance semantics;
3. unique encoding and round trips;
4. raw language and certificate semantics;
5. occurrence reduction semantics;
6. total raw map and cubic output bound;
7. concrete reduction machine;
8. concrete verifier and `GeneralCLIQUE ∈ NP`;
9. public `CLIQUE` migration;
10. status, progress, literate navigation, and proof audit.

Every checkpoint runs its narrow source build and interface test.  Final
acceptance additionally runs the Chapter 34 root build, repository checks,
placeholder scan, `git diff --check`, full library build, and `#print axioms`
for the headline semantic, reduction, verifier, and NP theorems.

## Explicit dependency and completion boundary

This subproject completes the honest CLIQUE language, proves its NP membership,
and proves the textbook 3-CNF-SAT-to-CLIQUE reduction.  It does not silently
claim `NPComplete CLIQUE` from those two facts alone.

The repository's universal NP-hardness theorem currently targets
`GeneralCircuitSAT`.  Transporting it through SAT and 3-CNF-SAT also requires a
concrete polynomial-time machine for the already proved semantic
`GeneralCircuitSAT`-to-`SAT` map.  Until that upstream bridge is implemented,
the exact remaining theorem is recorded as:

```lean
clique_npComplete : NPComplete CLIQUE
```

with the missing dependency named as the concrete
`GeneralCircuitSAT → SAT` reduction machine.  This is a representation-level
dependency, not a reason to weaken or overload the general CLIQUE definition.

## Non-goals

- No dual-format parser for the old `GraphSym` encoding.
- No website rendering or deployment.
- No VERTEX-COVER implementation in this specification.
- No replacement of the existing specialized occurrence theorem before the
  honest general reduction is available.
- No `sorry`, `admit`, project axiom, or theorem whose statement hides a
  machine assumption behind an unproved prose claim.
