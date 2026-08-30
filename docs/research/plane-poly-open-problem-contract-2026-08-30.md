# Plane Polychromatic Open Problem Research Contract

Date: 2026-08-30

Status: new research; target frozen, no claimed solution

## Phenomenon

- **Question:** Is plane polychromatic `k`-colorability NP-complete for every
  fixed `k >= 5`?
- **Why it matters:** It is an explicit unresolved complexity question left by
  the foundational 2009 paper, and a uniform color-lifting construction would
  explain the complexity of all remaining fixed palette sizes.
- **Falsifier for the selected route:** A fixed `k >= 4` for which no proposed
  lift preserves both plane faces and colorability, witnessed by a valid source
  coloring or target coloring violating one direction of the claimed `iff`.

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
| semantic lift | finite construction plus coloring `iff` and exact face proof | a polynomial-time reduction |
| resolves `k = 5` | proves NP-completeness for the first unknown fixed case | resolves every `k >= 5` |
| resolves Open Problem 2 | proves every fixed `k >= 5` case | verifies a gadget or known base case |

## Research-question map

| RQ | Question | Evidence required | Allowed claim |
|---|---|---|---|
| RQ1 | Does a composable plane palette/equality gadget exist for five colors? | exact face list plus exhaustive and structural extension/force proofs | a valid local gadget exists |
| RQ2 | Does the gadget yield a `4 -> 5` coloring-preserving plane transformation? | global gluing, face correctness, extension, restriction, size bound | the first unknown semantic reduction is proved |
| RQ3 | Can the lift be parameterized from `k` to `k+1`? | one theorem quantified over `k >= 4` | all remaining hardness cases follow from the `k = 4` base |
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
| a candidate finite gadget satisfies its contract | fail until checked | future exhaustive witness and Lean theorem | outer face and gluing must be included | solved from a drawing or selected examples |
| `k = 5` is NP-complete | fail until proved | future semantic and polynomial-time reduction plus NP membership | does not settle `k >= 6` | Open Problem 2 completely solved |
| every fixed `k >= 5` case is NP-complete | fail until proved | quantified lift, `k = 4` base, NP membership, honest complexity bridge | requires final literature and independent audits | solved before all gates pass |

## Open risks

- The all-different equality idea may have no composable plane realization
  because of its outer face.
- Local palettes may fail to synchronize a common filler-color set globally.
- A valid `k = 5` gadget may not admit a uniform `k -> k+1` family.
- Plane-map gluing and concrete encoding may dominate the Lean workload even
  after the mathematical gadget is known.
- Later literature or direct expert feedback may show that the proposed result
  is known under different terminology.
- The relation to 3D-IC layout is conceptual; no EDA performance or repair
  claim follows from this complexity theorem.

