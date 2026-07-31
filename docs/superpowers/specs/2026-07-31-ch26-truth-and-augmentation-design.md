# Chapter 26 Status Truth and Augmentation Design

**Status:** Approved for implementation on 2026-07-31 through the user's
instruction to follow the recommended Chapter 26 proof order.

## Goal

First make the Chapters 1--26 remaining-work ledger agree with the declarations
that actually compile on `main`.  Then build the first missing Chapter 26 core
layer: a real residual-path augmentation whose result is a feasible flow with
strictly larger value.

This design follows the repository's selected-section boundary.  It does not
require reproducing every chapter HTML page or every low-level implementation.

## Fixed status boundary

The current source proves 8 of the 8 reader-facing Chapter 26 groups that are
actually represented.  It does not prove Lemma 26.7.  The progress row must
therefore change from `9/9` with three missing groups to `8/8` with four missing
groups:

1. Lemma 26.7, including the predecessor/prefix and augmentation-edge bridge;
2. concrete augmentation, strict value increase, and the full max-flow/min-cut
   equivalence;
3. an executable BFS/Edmonds--Karp loop and the abstract `O(VE^2)` work bound;
4. matching-to-feasible-flow, integral-flow-to-matching, and the maximum-value
   equivalence of Theorem 26.12.

Sections 26.4 and 26.5 are not represented.  They remain explicitly deferred
outside this selected milestone and are not added to these four blockers.

The same reconciliation pass also removes known stale prose for Chapters 7,
14, 17, 19, and 24:

- Chapters 7 and 24 already have the bridges that `CLRSLean/Status.lean` still
  calls missing.
- Chapter 14 has a generic executable deletion pipeline and
  `wellAugmented_delete`; only the generic `toRB_delete` semantic erasure bridge
  remains a refinement target.
- Chapter 17 is selected-section complete; allocator/RAM work does not reopen
  that milestone.
- Chapter 19 already has the concrete `FTree` Fibonacci subtree-size and
  logarithmic degree theorem.  Its central remaining work is the executable
  heap-forest/cut/consolidation/amortization layer, not that static theorem.

This pass does not downgrade Chapters 6 or 14 in the CSV.  Their tighter cost
and generic-erasure targets remain visible boundary refinements.  A later
milestone may deliberately widen either completion contract, but this Chapter
26 repair does not silently change those contracts.

## Approaches considered

### A. Simple residual path plus concrete augmentation -- selected

Represent an augmenting path by a nonempty, duplicate-free vertex list with
source and sink endpoints and a residual edge between every consecutive pair.
Derive its edge list, positive bottleneck, antisymmetric flow update, feasibility,
conservation, and strict value increase.  Prove that residual reachability
provides such a path, then derive `hasAugmentingPath -> not isMaximal`.

This route exposes the central Ford--Fulkerson argument and gives later
Edmonds--Karp proofs a concrete path/update relation.

### B. Abstract augmentation certificate

Assume a direction matrix together with capacity, conservation, and value
properties, and package it as a new flow.  This would make the first proofs
shorter, but it would move the hard path-to-update argument into hypotheses and
would not close the Chapter 26 core gap.

### C. Restore historical Lemma 26.7 first

Port the 402-line proof from `e7c2dd3` before defining a real augmentation.
This gives a headline theorem quickly, but its abstract
`h_new_edge_reverse` hypothesis is not yet derived from an algorithmic step.
It would reproduce the same disconnect that allowed the current ledger drift.

## Proof architecture

### Existing base layer

`CLRSLean/Chapter_26/Section_26_1_Flow_Networks.lean` remains the base model.  It
owns `FlowNetwork`, `Flow`, residual capacity/edges, reachability, cut bounds,
and `maximal_of_noAugmentingPath`.

The existing `Flow` model uses real capacities and skew-symmetric net flow.  A
single finite augmentation is valid over `Real`; termination of arbitrary
Ford--Fulkerson choices is not claimed.  Edmonds--Karp termination and work are
separate later milestones.

### New augmentation layer

Create
`CLRSLean/Chapter_26/Section_26_2_Ford_Fulkerson_Augmentation.lean`.
It will contain one focused family:

- `ResidualPath`: a source-to-sink simple residual path;
- `ResidualPath.edges`: consecutive directed edges;
- `ResidualPath.bottleneck`, with positivity and per-edge upper bounds;
- a signed path update that adds the bottleneck on forward path edges and
  subtracts it on their reverses;
- skew-symmetry, capacity, and internal-vertex conservation lemmas for that
  update;
- `ResidualPath.augment : Flow V G`;
- `ResidualPath.augment_value` and strict-value wrapper;
- extraction of a simple residual path from `Flow.hasAugmentingPath`;
- `Flow.not_maximal_of_hasAugmentingPath`.

The path is simple so an ordered edge and its reverse cannot both occur and no
edge is augmented twice.  This keeps the capacity proof local.  Conservation
is proved by a signed-incidence/telescoping lemma: an internal vertex has one
incoming and one outgoing path contribution; the source has net `+delta`; the
sink has net `-delta`.

The existing `ResidualPathLength` remains the distance-oriented representation
for Section 26.2.  A later bridge will relate a shortest concrete
`ResidualPath` to `ShortestAugmentingPath`; the augmentation layer does not
replace the distance API.

### Max-flow/min-cut packaging

After strict augmentation compiles, refactor the reachable cut currently local
to `Flow.maximal_of_noAugmentingPath` into public cut-certificate lemmas.  Then
package:

- `Flow.isMaximal_iff_noAugmentingPath`;
- existence of a source/sink cut whose capacity equals the flow value;
- the three-condition max-flow/min-cut equivalence.

This packaging must reuse the concrete augmentation theorem; it must not assume
the missing direction as a certificate.

## Public proof surface and TDD

The status commit adds `Tests/Chapter_26_Interface.lean`, containing only
declarations that exist before new proof work.  It protects the honest partial
surface without keeping a deliberately failing test on `main`.

Before production augmentation code, add
`Tests/Chapter_26_Augmentation_Interface.lean` with the intended headline names
and run it to observe `unknownIdentifier`.  Add only names that are intended as
stable public API.  Helper lemmas remain private until downstream use justifies
them.

Before restoring Lemma 26.7, add
`Tests/Chapter_26_Edmonds_Karp_Interface.lean` with
`#check CLRS.Chapter26.shortest_path_nondec`, verify the expected RED failure,
then implement and turn it GREEN.

## Documentation changes

The truthfulness commit updates:

- `docs/clrs-proof-progress.csv`;
- generated `CLRSLean/Progress.lean` and the generated README table;
- `CLRSLean/Chapter_26.lean` and the Section 26.2/26.3/26.6 docstrings;
- `CLRSLean/Status.lean`;
- `docs/proof-map.md` and `docs/proof-status-board.md`;
- stale supplementary guides for Chapters 17 and 19;
- Chapter 26 titles in `literate.toml`;
- `Tests/Chapter_26_Interface.lean`.

The legacy file name `Section_26_6_MaxFlow_MinCut.lean` is not renamed in this
pass.  Its heading is corrected to explain that it formalizes CLRS Theorem 26.6;
a rename would add unrelated import/navigation churn.

## Commit boundaries

1. `docs(progress): reconcile remaining Chapter 26 gaps`
   - status sources, generated summaries, stale prose, and current interface
     test only;
   - no new theorem claim.
2. `feat(ch26): add residual-path augmentation foundation`
   - concrete path, bottleneck, feasible augmentation, strict value increase,
     and focused interface test.
3. `feat(ch26): complete max-flow min-cut equivalence`
   - reachability-to-path bridge if not already included, nonmaximality from an
     augmenting path, public cut certificate, and equivalence wrappers.

Each commit gets narrow Lean checks before the repository-wide gate.

## Verification

Status commit:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_26_Interface.lean
lake build CLRSLean.Chapter_26
uv run python scripts/check_progress_csv.py --write-dashboard
python3 scripts/gen_readme_table.py
python3 scripts/check_repository.py
git diff --check
```

Proof commits:

```bash
lake build CLRSLean.Chapter_26.Section_26_2_Ford_Fulkerson_Augmentation
lake env lean -DwarningAsError=true Tests/Chapter_26_Augmentation_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_26_Interface.lean
lake build CLRSLean.Chapter_26
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_26 Tests/Chapter_26_*.lean
python3 scripts/check_repository.py
git diff --check
```

Site-visible completion claims additionally require `lake build :literateHtml`.

## Success criteria

- No current document claims that Lemma 26.7 exists before it compiles.
- Ch26 is reported as `8/8` represented groups with four explicit core gaps.
- Existing Ch7/14/17/19/24 prose no longer names already-closed work as open.
- The current Ch26 public surface has a compiling interface test.
- The first proof milestone constructs a feasible, strictly higher-value flow
  from a concrete residual path without hidden augmentation assumptions.
- No `sorry`, `admit`, or project axiom enters an imported Chapter 26 module.
