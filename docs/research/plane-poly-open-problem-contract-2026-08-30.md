# Plane Polychromatic Open Problem Research Contract

Date: 2026-08-30

Status: new research; target frozen, first global route falsified, no claimed
solution

## Phenomenon

- **Question:** Is plane polychromatic `k`-colorability NP-complete for every
  fixed `k >= 5`?
- **Why it matters:** It is an explicit unresolved complexity question left by
  the foundational 2009 paper, and a uniform color-lifting construction would
  explain the complexity of all remaining fixed palette sizes.
- **Falsifier for a selected route:** either a coloring counterexample to one
  direction of its claimed `iff`, or a legal source instance for which the
  required constraint skeleton cannot be embedded in the plane.  The first
  Hamilton-path route has been falsified by the latter kind of obstruction.

## Unit and universe

- **Primary unit:** one finite encoded combinatorial plane map at one fixed
  color count `k`.
- **Universe:** all well-formed finite plane-map encodings, including the
  unbounded face; malformed encodings are rejected by the language.
- **Inclusion:** fixed `k >= 5`, actual face-orbit semantics, every face must
  contain all `k` colors.
- **Exclusion:** abstract hypergraphs without a realized plane embedding,
  bounded-size graph samples, geometric drawings with unchecked crossings,
  and promise subclasses unless their equivalence to the full problem is
  proved.
- **Denominator for gadget enumeration:** every assignment of `Fin k` to all
  vertices of the finite candidate gadget, modulo only explicitly proved color
  symmetries.
- **Known missingness:** no plane-map library or accepted palette gadget exists
  in the current repository.

## Terms

| Term | Definition | Do not confuse with |
|---|---|---|
| plane graph | graph together with a fixed cellular plane embedding | a planar graph with no supplied embedding |
| face | orbit of the face-successor permutation, with incident colors deduplicated by vertex | an arbitrary listed hyperedge |
| polychromatic `k`-coloring | every face sees every member of `Fin k` | proper graph coloring |
| semantic reduction | finite construction plus coloring `iff` and exact face proof | a polynomial-time reduction |
| resolves `k = 5` | proves NP-completeness for the first unknown fixed case | resolves every `k >= 5` |
| resolves Open Problem 2 | proves every fixed `k >= 5` case | verifies a gadget or known base case |

## Research-question map

| RQ | Question | Evidence required | Allowed claim |
|---|---|---|---|
| RQ1 | Do the theta equality and pendant-cycle neutralizer satisfy their contracts for every `k >= 5`? | exact face list plus general extension/force proofs | the local constraint basis is valid |
| RQ2 | Why does the supplied-Hamilton-path lane construction fail? | topological contraction argument plus one legal source counterexample | the first global route is rigorously rejected |
| RQ3 | Can an annular palette patch around a supplied Hamiltonian cycle expose source-edge ports on both sides while preserving every intended face? | explicit rotation system, face enumeration, extension, restriction, and size bound | a replacement semantic reduction is viable |
| RQ4 | Is the target language honestly NP-complete in CLRS-Lean? | concrete verifier and reduction machines with polynomial runtime | kernel-checked resolution of the complexity question |

## Canonical artifacts

| Artifact | Purpose | Generated | Hand-edited? |
|---|---|---|---|
| `docs/superpowers/specs/2026-08-30-plane-poly-open-problem-design.md` | frozen mathematical and formal design | no | yes |
| `docs/research/plane-poly-open-problem-contract-2026-08-30.md` | claim and evidence boundary | no | yes |
| future canonical gadget witness under `data/research/plane-poly/` | exact vertices, darts, rotations, faces, terminals | by search/export tool | no |
| future Lean modules under `CLRSLean/Research/PlanePoly/` | kernel-checked definitions and proofs | no | yes |

## Claim ledger

| Claim | Status | Evidence | Caveat | Forbidden wording |
|---|---|---|---|---|
| Alon et al. explicitly posed the fixed-`k >= 5` NP-completeness question | support | original paper, Open Problem 2 | publication date is 2009; workshop origin is 2007 | invented by this project |
| the exact question remains open in 2026 | caution | no resolution found in the 2026-08-30 search | absence from search is not conclusive | definitively open without final citation/author audit |
| current affine-strip theorems solve part of this plane-graph problem | fail | none | the models share coloring ideas but not instances or semantics | prior ThreeDIC result resolves the public problem |
| the theta equality and pendant-cycle neutralizer satisfy their contracts | caution | exact-`k` face argument recorded in the revised design | global attachment and face enumeration remain unproved | solved from the local drawing alone |
| traceable planar 3-colorability is NP-complete | support | Havet, King, Liedloff, and Todinca, Discrete Applied Mathematics 169 (2014), Lemma 26 | final proof must use the source's supplied Hamilton path and plane embedding | ordinary planar 3-colorability automatically supplies a path |
| the Hamilton-path palette-lane reduction works | fail | contraction yields a forbidden planar Hamiltonian augmentation; maximal planar traceable non-Hamiltonian graphs witness failure | local coloring gadgets can remain valid despite global failure | uniform reduction or open problem solved |
| planar Hamiltonian 3-coloring is NP-hard even with the Hamiltonian cycle supplied | support | Cavallaro and Fluschnik (2021), Theorem 1 and introduction | this source theorem does not itself provide the required target embedding | Hamiltonian-cycle source automatically solves the palette-routing problem |
| a uniform semantic reduction exists for every fixed `k >= 5` | fail until proved | future annular station construction or a different route | the path-based construction is rejected | open problem solved |
| `k = 5` is NP-complete | fail until proved | future semantic and polynomial-time reduction plus NP membership | does not settle `k >= 6` | Open Problem 2 completely solved |
| every fixed `k >= 5` case is NP-complete | fail until proved | a valid uniform plane reduction, NP membership, and honest complexity bridge | requires final literature and independent audits | solved before all gates pass |

## Open risks

- The theta gadget is locally sound, but an external attachment in the wrong
  rotation angle can destroy one of its intended faces.
- A Hamiltonian cycle avoids the endpoint augmentation obstruction, but its
  chords can lie on both sides; the annular station patch may still be
  impossible.
- The face neutralizer uses a bridge and therefore proves the unrestricted
  plane-graph problem, not a stronger 2-connected restriction.
- Plane-map gluing and concrete encoding may dominate the Lean workload even
  after the mathematical gadget is known.
- Later literature or direct expert feedback may show that the proposed result
  is known under different terminology.
- The relation to 3D-IC layout is conceptual; no EDA performance or repair
  claim follows from this complexity theorem.
