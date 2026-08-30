# Plane Polychromatic NP-Completeness Open Problem Design

Date: 2026-08-30

Status: design approved in conversation; implementation has not started

## Research target

The final target is Open Problem 2 of Alon, Berke, Kevin Buchin, Maike Buchin,
Csorba, Shannigrahi, Speckmann, and Zumstein, *Polychromatic Colorings of
Plane Graphs* (Discrete & Computational Geometry 42, 2009):

> Is `PLANE-POLY-k-COLORABILITY` NP-complete for every fixed `k >= 5`?

The paper proves the cases `k = 3` and `k = 4` and explicitly leaves every
fixed `k >= 5` open.  Its author-hosted version is
<https://www.tau.ac.il/~nogaa/PDFS/polychromatic.pdf>; the journal record is
<https://link.springer.com/article/10.1007/s00454-009-9171-5>.

The literature audit performed on 2026-08-30 found no later resolution of the
exact question.  Failure to find a paper is not proof that the question is
still open.  Before any public novelty claim, the project must complete
backward and forward citation tracing and seek confirmation from an expert or
an original author.

## Completion criteria

The full goal is achieved only by a proof that, for every fixed natural number
`k >= 5`, deciding whether a finite plane graph has a vertex `k`-coloring in
which every face contains every color is NP-complete.

The proof must contain all of the following:

1. an explicit, finite, plane construction for every required instance;
2. a proof that the listed faces are exactly the faces of the constructed
   embedding, including the unbounded face;
3. a forward coloring-extension theorem;
4. a reverse coloring-restriction theorem;
5. a polynomial output-size and construction-time bound;
6. membership of the fixed-`k` language in NP;
7. NP-hardness from a previously NP-hard language;
8. a Lean theorem exposing the fixed-`k` NP-completeness result without
   `sorry`, `admit`, new axioms, or bounded enumeration standing in for the
   general proof.

Proving only `k = 5` settles the first unknown case and is a potentially
publishable partial result, but it does not complete the stated open problem.
A verified finite gadget, a bounded SAT search, or a semantic reduction that
omits its plane embedding or polynomial-time implementation is progress, not a
resolution.

## Approaches considered

### A. A parameterized color-lifting reduction (recommended)

Construct a plane transformation

```text
Lift(k) : PLANE-POLY-k -> PLANE-POLY-(k+1)
```

with extension and restriction in both directions.  The known NP-complete
`k = 4` case would then imply every fixed `k >= 5` by induction.  This is the
only route among those considered that naturally resolves the whole open
problem with one mathematical mechanism.

The main obstacle is a plane palette-propagation gadget.  A face with exactly
`k` distinct boundary vertices acts as an `AllDifferent(k)` constraint.  Two
such constraints sharing `k - 1` terminals semantically force their remaining
terminals to have the same color.  However, a graph drawing that realizes the
two intended faces usually creates another face.  The construction is valid
only if every unintended and exterior face is also polychromatic and the
gadget remains composable inside a plane disk.

### B. A direct reduction for `k = 5`

Generalize the published `k = 4` reduction from plane proper 3-colorability.
This lowers the first mathematical target and may reveal the missing palette
gadget.  It can settle the first unknown case, but without a parameterized
argument it leaves all `k >= 6` open.  It is therefore a fallback and a
feasibility milestone inside Approach A, not a replacement final objective.

### C. Determine the extremal number `p(5)`

The same paper's Open Problem 1 asks for the exact minimum polychromatic number
at face size five.  It is a genuine long-standing problem, but it is less
connected to Chapter 34 and appears to require a global structural or
discharging theorem.  Finite counterexample search would not settle the
likely universal direction.  This route is not selected.

Golomb--Welch is also a genuine long-standing conjecture, but the present
repository lacks the coding-theory and lattice-tiling infrastructure needed to
make it a tractable first target.

## Mathematical architecture

### Plane maps rather than abstract face hypergraphs

The formal object will be a finite combinatorial plane map, not an arbitrary
graph plus a user-supplied list of constraints.  A map consists of finite
darts, a fixed-point-free edge reversal, a cyclic vertex rotation, and a
distinguished outer face orbit.  Faces are orbits of the standard face
successor permutation.  Connected maps must satisfy the genus-zero Euler
equation `V - E + F = 2`; a rotation system without this condition may encode
a cellular embedding on a higher-genus orientable surface and is not accepted
as a plane map.  This makes face preservation auditable and prevents a
hypergraph reduction from being mislabeled as a plane-graph reduction.

The first implementation stage may use an explicit finite disk-patch
structure for gadget discovery.  A disk patch records its boundary terminals,
interior darts, face walks, and an exterior boundary walk.  A gluing theorem
must translate a valid patch composition into a valid combinatorial plane map.

### Coloring semantics

For fixed `k`, a coloring maps vertices to `Fin k`.  It is polychromatic when
the set of colors on the vertices incident with every face is `Finset.univ`.
Repeated occurrences of a cut vertex on a facial walk do not create new
colors; the semantics therefore uses the image set of incident vertices, not
the length of the facial walk.

The definitions must cover loops, parallel edges, bridges, repeated facial
vertices, disconnected input encodings, and the unbounded face explicitly.
The reduction may first normalize to connected loopless source instances, but
that restriction must be proved semantics-preserving.

### Gadget contracts

Gadgets are specified by behavior, not by a drawing alone.

An equality gadget for fixed `k` has two boundary terminals `x` and `y` and
must prove:

```text
force:   every valid internal coloring has color(x) = color(y)
extend:  every choice of one terminal color extends with color(x) = color(y)
```

A palette gadget has ordered boundary terminals `p[0], ..., p[k-1]` and must
prove that every valid coloring assigns all `k` colors bijectively, and that
every permutation of the palette extends.  Palette propagation must preserve
the same palette roles across adjacent source faces without using a single
nonplanar global palette vertex set.

A lift gadget must additionally prove:

```text
extension:   every k-polychromatic source coloring extends to k+1 colors
restriction: every (k+1)-polychromatic target coloring determines a
             k-polychromatic source coloring, modulo a global color permutation
```

All contracts quantify over every coloring.  SAT or exhaustive enumeration
may discover a candidate and may certify one fixed finite truth table, but the
structural proof must explain why a parameterized family satisfies the
contract.

### Global reduction theorem

Given a valid connected plane source map, replace each selected face/edge by a
copy of the disk gadget, glue copies along their declared boundary walks, and
prove:

```text
source is k-polychromatically colorable
  iff
Lift(k, source) is (k+1)-polychromatically colorable.
```

The construction proof is split into:

1. finite well-formedness and fresh-name disjointness;
2. gluing and exact face enumeration;
3. coloring extension;
4. palette synchronization and coloring restriction;
5. linear or polynomial vertex/dart/face size bounds.

The induction from the published `k = 4` base case is performed only after the
single-step theorem is complete.

## Complexity and Chapter 34 integration

The decision language encodes a finite combinatorial map, not merely an
unembedded graph.  A deterministic verifier checks the permutation fields,
edge pairing, rotations, face traversal, coloring certificate, and the
all-colors-on-every-face predicate in polynomial time for each fixed `k`.

Chapter 34 supplies the definitions and transport theorems
`PolyTimeReducible`, `NPHard.of_reducible`, and
`NPComplete.of_reducible`.  The reduction will first expose a semantic
function, correctness theorem, and polynomial output-length certificate.  It
does not become a `PolyTimeReducible` theorem until a concrete polynomial-time
machine computes the same encoding.  Existing Cook--Levin and PolyBuilder
infrastructure may be reused for this last bridge; stipulated costs or an
unimplemented compiler are not acceptable.

## File boundaries

The proof is intentionally split into small files because Lean does not
incrementally compile declarations within one large file.

```text
CLRSLean/Research/PlanePoly/
  CombinatorialMap/Basic.lean
  CombinatorialMap/Faces.lean
  CombinatorialMap/DiskPatch.lean
  CombinatorialMap/Gluing.lean
  Coloring/Semantics.lean
  Gadget/Contract.lean
  Gadget/Equality.lean
  Gadget/Palette.lean
  Reduction/LiftConstruction.lean
  Reduction/FaceCorrectness.lean
  Reduction/ColoringExtension.lean
  Reduction/ColoringRestriction.lean
  Reduction/SizeBound.lean
  Encoding/Basic.lean
  Encoding/Verifier.lean
  Encoding/PolynomialRuntime.lean
  NPCompleteness.lean
```

Candidate-gadget search code, if used, lives under `scripts/research/` and
produces a canonical machine-readable witness.  It is not imported as a proof
of the general theorem.

Public theorem names and exact applications are frozen in small interface
tests before each production module is written.  Only focused modules and
their interfaces are compiled during development; the full repository gate is
reserved for milestone completion.

## Feasibility sprint and stopping rules

The first sprint is mathematical and must not prematurely build the entire NP
encoding stack.  It will:

1. formalize the disk-gadget contract on paper and in a small executable model;
2. test the shared-`k-1` all-different equality idea against all faces;
3. search for or construct a five-color palette propagation gadget;
4. independently enumerate every coloring of any finite candidate;
5. either produce a checked `4 -> 5` semantic lift or a concrete obstruction
   explaining why the candidate family fails.

The approach is rejected or redesigned if any of these occurs:

- an alleged gadget ignores its outer face;
- two intended faces cannot coexist in the claimed plane embedding;
- palette copies choose inconsistent filler-color sets;
- original vertices can use filler colors in a reverse coloring;
- the result is only an abstract hypergraph CSP;
- the reduction works only under an unproved promise on the source embedding;
- a later literature audit finds the exact result already published.

A failed candidate is recorded as a counterexample-backed research result,
not silently patched by weakening the theorem.

## Verification and publication gate

Every public theorem receives:

- a missing-declaration RED interface test;
- exact theorem-application examples, not bare `#check` alone;
- boundary regressions for `k = 5`, the exterior face, bridges, repeated facial
  vertices, and palette permutations;
- `#print axioms` trust checks on headline theorems;
- declaration-aware scans for `sorry`, `admit`, `axiom`, and `native_decide`;
- focused builds during development and a fresh `lake build CLRSLean` only at
  a completed milestone;
- an independent mathematical review of planarity, both coloring directions,
  complexity, and claim wording.

No paper or README may say that the open problem is solved until the full
fixed-`k >= 5` theorem, honest polynomial-time reduction, literature audit,
and independent review all pass.  If only `k = 5` is proved, the allowed claim
is exactly that the first previously unknown fixed-color case is settled.
