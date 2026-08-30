# Plane Polychromatic NP-Completeness Open Problem Design

Date: 2026-08-30

Status: open target frozen; first global reduction rejected by topological
counterexample; replacement route under mathematical audit

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

### A. A uniform direct reduction from traceable planar 3-colorability
(rejected)

For each fixed `k >= 5`, reduce from `TRACEABLE PLANAR 3-COLOURABILITY`: the
input is a plane graph together with a Hamilton path and the question is
whether it is properly 3-colorable.  Lemma 26 of Havet, King, Liedloff, and
Todinca, *(Circular) Backbone Colouring: Forest Backbones in Planar Graphs*,
Discrete Applied Mathematics 169 (2014), proves this problem NP-complete
(<https://doi.org/10.1016/j.dam.2014.01.011>).

The Hamilton path gives a nonbranching plane route through every source vertex.
Along a thin regular neighborhood of that path, `k - 3` serial equality lanes
propagate a common set of forbidden colors.  A facial `k`-cycle at every source
vertex contains the local lane terminals, the source vertex, and two fresh
vertices.  It therefore restricts every source vertex to the same three-color
complement.  A facial `k`-cycle in a thin lens around every source edge forces
its endpoints to receive distinct colors.

The remaining obstacle is not color semantics but exact face control.  After
the constraint skeleton is complete, every nonconstraint face is neutralized
by placing a fresh `k`-cycle inside it and joining that cycle to the old face
boundary by one bridge.  The new inner face forces the cycle to contain all
colors; the modified old face is incident with that same cycle and is therefore
automatically polychromatic.  This includes the unbounded face.

Independent review found a fatal obstruction.  For any one equality-lane
coordinate, the lane chain gives a fresh path between the two Hamilton-path
end stations.  Together with the source Hamilton path as realized by the edge
lenses, this creates a cycle through every source vertex.  Contracting the
fresh paths would therefore give a plane embedding after adding the edge
between the Hamilton-path endpoints.  Traceable planar graphs do not satisfy
that promise: a maximal planar non-Hamiltonian graph with a Hamilton path is a
counterexample.  Hence this route cannot reduce all legal source instances and
must not be implemented or described as a solution.

### A2. A Hamiltonian-cycle source (under audit)

Cavallaro and Fluschnik prove that 3-coloring remains NP-hard for planar
Hamiltonian graphs even when a Hamiltonian cycle is supplied with the input
(*3-Coloring on Regular, Planar, and Ordered Hamiltonian Graphs*, 2021,
<https://arxiv.org/abs/2104.08470>).  Replacing the path by its already present
Hamiltonian cycle removes the endpoint-augmentation counterexample: a closed
palette lane can be homotopic to the supplied cycle instead of forcing a new
edge.

This is only a replacement candidate, not yet a valid reduction.  A
Hamiltonian cycle separates the plane into two disks, and non-cycle edges may
occur on both sides.  The next feasibility obligation is an explicit annular
station patch whose source vertex and edge-lens ports remain accessible from
both sides while all palette coordinates propagate around the cycle and every
constraint cycle remains facial.  No semantic or Lean implementation begins
until a rotation system for that patch is exhibited and checked.

### B. A parameterized color-lifting reduction

Construct `PLANE-POLY-k <=p PLANE-POLY-(k+1)` and induct from the known
`k = 4` case.  This remains a fallback if the direct Hamilton-path embedding
fails.  It requires a more difficult palette-copy construction around every
source face and currently has no comparably explicit global embedding.

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

### Candidate gadget contracts

Gadgets are specified by behavior, not by a drawing alone.  The feasibility
audit produced the following explicit parameterized candidates.

The equality gadget `Eq(k, x, y)` is a theta graph.  Let `P` be a path from
`a` to `b` containing exactly `k - 1` distinct vertices.  Add the two length-two
paths `a-x-b` and `a-y-b`, embedded on opposite sides of `P`.  The cycles
`P + x` and `P + y` are facial `k`-cycles.  Hence:

```text
force:   every polychromatic coloring has color(x) = color(y), because both
         terminals are the unique color missing from the shared rainbow P;
extend:  if color(x) = color(y), assign every other color bijectively to P.
```

External edges at `x` and `y` must be placed only in their outer-face angles,
so the two intended faces survive composition.  The third theta face is not
assumed valid; it is neutralized after the entire skeleton is embedded.

For Hamilton-path vertex `v_i`, introduce lane terminals
`a_i^1, ..., a_i^(k-3)` and fresh vertices `s_i,t_i`.  Make

```text
(a_i^1, ..., a_i^(k-3), v_i, s_i, t_i)
```

a facial `k`-cycle.  Equality gadgets join `a_i^j` to `a_(i+1)^j` for every
consecutive path position and lane `j`.  Every station palette is therefore
the same ordered set of `k - 3` distinct colors, and every source vertex uses
one of the common three remaining colors.

For every source edge `uv`, a thin facial lens has boundary `u`, `v`, and
`k - 2` fresh vertices.  Its exact `k` vertices force `color(u) != color(v)`
and can be extended by assigning the other `k - 2` colors to the fresh
vertices.

For every residual face `f`, the face-neutralizer places a disjoint fresh
`k`-cycle `C_f` in `f` and adds one bridge from a boundary vertex of `f` to one
vertex of `C_f`.  The interior of `C_f` is a facial `k`-cycle.  The other side
of `C_f` remains part of the modified `f`, so both new faces see every color.
This gadget imposes no constraint on the old boundary coloring.

All contracts quantify over every coloring.  Finite enumeration may check
small instances, but the final proof uses the exact-`k` face argument for
arbitrary `k`.

### Rejected path-based global theorem

Let `(G,P)` be a connected simple plane graph with a supplied Hamilton path
`P = v_1,...,v_n`.  Construct the station cycles and equality lanes in a thin
regular neighborhood of `P`.  Put every edge lens in a disjoint thin
neighborhood of its source edge, reserving the opposite substrip for the lanes
on path edges.  Equality-gadget attachments occur only through their outer
angles.  After the complete constraint skeleton is embedded, insert one
neutralizer into every residual face.

The proposed theorem was

```text
G is properly 3-colorable
  iff
planePoly(k, reduce(k,G,P))
```

for every fixed `k >= 5`.  Its coloring argument remains conditionally valid,
but its plane construction is false for the reason above, so this is not an
available theorem target.

Forward, choose any three target colors for the source coloring, put the other
`k - 3` colors on every station palette in one fixed order, fill each equality
path with the remaining colors, fill edge lenses with all colors missing from
their two endpoints, and color every neutralizer cycle bijectively.

Reverse, station faces make each local palette pairwise distinct; the equality
lanes make all palettes coordinatewise equal.  Thus all source vertices use
one common set of at most three colors.  Every source edge is a pair of
vertices on an exact facial `k`-cycle, hence its endpoints differ.  Renaming
the common complement yields a proper `Fin 3` coloring of `G`.

Any replacement construction must still supply:

1. finite well-formedness and fresh-name disjointness;
2. a rotation-level tubular-neighborhood embedding theorem;
3. preservation and exact enumeration of all intended faces;
4. exhaustive enumeration and neutralization of all residual faces;
5. coloring extension and restriction;
6. `O(k^2 |V| + k |E|)` skeleton size and linear neutralization overhead for
   each fixed `k`.

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
  Gadget/Station.lean
  Gadget/EdgeLens.lean
  Gadget/FaceNeutralizer.lean
  Reduction/HamiltonianCycleSource.lean
  Reduction/ConstraintSkeleton.lean
  Reduction/TubularEmbedding.lean
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

1. prove the equality, station, edge-lens, and neutralizer contracts as abstract
   exact-face lemmas;
2. record the Hamilton-path augmentation counterexample as a rejected route;
3. construct and exhaustively enumerate an annular station patch with ports on
   both sides of a supplied Hamiltonian cycle, or reject this replacement;
4. only after that patch exists, attempt the full semantic `iff` for arbitrary
   fixed `k >= 5`;
5. obtain independent review of the source NP-hardness, embedding, both
   coloring directions, and the status of the 2009 question;
6. only then begin the serialized language and concrete runtime layers.

The approach is rejected or redesigned if any of these occurs:

- an alleged gadget ignores its outer face;
- two intended faces cannot coexist in the claimed plane embedding;
- palette lanes cannot be embedded without destroying an intended face;
- station palettes can differ despite the equality-lane hypotheses;
- original vertices can use a forbidden color in a reverse coloring;
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
