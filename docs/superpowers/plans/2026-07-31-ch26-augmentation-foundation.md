# Chapter 26 Concrete Augmentation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: use
> `superpowers:test-driven-development`, `lean-proof-engineering`, and
> `superpowers:verification-before-completion`.  Implement one task at a time
> and keep the RED interface test uncommitted until its declarations compile.

**Goal:** Turn a concrete simple residual source-to-sink path into a feasible
flow of strictly larger value, then connect residual reachability to such a
path and package the missing Max-Flow Min-Cut direction.

**Architecture:** Add a focused augmentation module above the existing flow
network model and below Edmonds-Karp.  A residual path is an ordered, duplicate-
free vertex list.  Its consecutive edges have a positive finite bottleneck.
An antisymmetric signed path delta is added to the old flow; telescoping proves
conservation and exact value increase.  A separate follow-up layer erases
cycles from a residual walk, obtains a simple augmenting path from the existing
reflexive-transitive reachability predicate, and derives maximality/cut
equivalences.

**Tech Stack:** Lean 4, Mathlib `List.IsChain`, `Relation.ReflTransGen`, finite
sums, real linear arithmetic, repository interface tests, and Git.

---

## Fixed proof boundary

This plan closes the first of the four recorded Chapter 26 gaps.  It does not
implement BFS, the Edmonds-Karp loop, Lemma 26.7, or the matching/integral-flow
bridge.  It does not claim termination for arbitrary real-capacity
Ford-Fulkerson choices.

The current flow model is skew-symmetric net flow and permits negative
`φ.f u v`.  Every capacity proof must therefore use only
`φ.hcapacity`, `φ.hskew_symm`, and residual capacity; it must not assume
pointwise nonnegative flow.  Anti-parallel capacities are allowed.

The stable public augmentation surface is:

```lean
Flow.ResidualPath
Flow.AugmentingPath
Flow.ResidualPath.edges
Flow.ResidualPath.residualEdge_of_mem_edges
Flow.AugmentingPath.edges_nonempty
Flow.AugmentingPath.bottleneck
Flow.AugmentingPath.bottleneck_pos
Flow.AugmentingPath.bottleneck_le_residualCapacity
Flow.augmentBy
Flow.augment
Flow.augmentBy_value
Flow.augment_value
Flow.value_lt_augment
```

The follow-up MFMC surface is:

```lean
Flow.hasAugmentingPath_iff_nonempty_augmentingPath
Flow.not_maximal_of_augmentingPath
Flow.not_maximal_of_hasAugmentingPath
Flow.maximal_iff_noAugmentingPath
Flow.exists_cut_value_eq_of_noAugmentingPath
Flow.maximal_iff_exists_cut_value_eq
```

Internal signed-incidence helpers may remain implementation details unless a
later proof imports them.

## Task 1: Lock the intended interface RED

**Files:**

- Create: `Tests/Chapter_26_Augmentation_Interface.lean`

- [ ] Add `#check` statements for the stable augmentation surface above.
- [ ] Import `CLRSLean.Chapter_26` so the test exercises the chapter's public
  import surface rather than a private module.
- [ ] Run:

```bash
lake env lean Tests/Chapter_26_Augmentation_Interface.lean
```

Expected RED result: `unknown identifier` for the new names.  Record the
failure in the work log; do not commit a deliberately failing test.

## Task 2: Define concrete simple residual paths

**Files:**

- Create:
  `CLRSLean/Chapter_26/Section_26_2_Ford_Fulkerson_Augmentation.lean`

- [ ] Import only `Section_26_1_Flow_Networks` plus Mathlib.
- [ ] Define:

```lean
structure Flow.ResidualPath
    (φ : Flow V G) (u v : V) where
  vertices : List V
  chain : vertices.IsChain φ.residualEdge
  head_eq : vertices.head? = some u
  last_eq : vertices.getLast? = some v
  nodup : vertices.Nodup

abbrev Flow.AugmentingPath (φ : Flow V G) :=
  Flow.ResidualPath φ G.s G.t
```

- [ ] Define `ResidualPath.edges := vertices.consecutivePairs`.
- [ ] Move or generalize the existing consecutive-chain helper from
  `Section_26_6_MaxFlow_MinCut.lean`; avoid duplicate public lemmas.
- [ ] Prove every member of `edges` is a residual edge.
- [ ] Prove an augmenting path has a nonempty edge list from its source/sink
  endpoints and `G.hs_ne_t`.
- [ ] Prove a simple path cannot contain both `(u,v)` and `(v,u)` as directed
  consecutive edges.
- [ ] Compile the new module after each theorem:

```bash
lake build CLRSLean.Chapter_26.Section_26_2_Ford_Fulkerson_Augmentation
```

## Task 3: Define the bottleneck and its bounds

**Files:**

- Modify:
  `CLRSLean/Chapter_26/Section_26_2_Ford_Fulkerson_Augmentation.lean`

- [ ] Form the finite nonempty set of residual capacities of path edges.
- [ ] Define the real-valued bottleneck with `Finset.min'`; the definition may
  be `noncomputable` because this layer is mathematical, not the later BFS
  implementation.
- [ ] Prove `bottleneck_pos` by taking the minimizing path edge and using the
  residual-edge chain.
- [ ] Prove `bottleneck_le_residualCapacity` for every path edge with
  `Finset.min'_le`.
- [ ] Add focused `#check`s to the RED test and recompile the module.

## Task 4: Prove signed path-delta algebra

**Files:**

- Modify:
  `CLRSLean/Chapter_26/Section_26_2_Ford_Fulkerson_Augmentation.lean`

- [ ] Define a signed one-edge delta and recursively sum it over consecutive
  vertices:

```lean
def Flow.edgeDelta (δ : ℝ) (a b u v : V) : ℝ :=
  (if u = a ∧ v = b then δ else 0) -
  (if u = b ∧ v = a then δ else 0)

def Flow.pathDelta (δ : ℝ) : List V → V → V → ℝ
```

- [ ] Prove `edgeDelta` and `pathDelta` are skew-symmetric.
- [ ] Prove the one-edge divergence sum and the telescoping path-divergence
  formula:

```lean
∑ v, Flow.pathDelta δ xs u v =
  (if xs.head? = some u then δ else 0) -
  (if xs.getLast? = some u then δ else 0)
```

- [ ] Prove the local evaluation theorem for a `Nodup` list: the delta is `δ`
  on a forward consecutive edge, `-δ` on its reverse, and `0` otherwise.
  This theorem is the single truth source for capacity preservation.
- [ ] Test degenerate lists (`[]`, `[u]`) in the proof rather than hiding them
  behind impossible augmenting-path assumptions.

## Task 5: Construct a feasible augmented flow

**Files:**

- Modify:
  `CLRSLean/Chapter_26/Section_26_2_Ford_Fulkerson_Augmentation.lean`

- [ ] Define `Flow.augmentBy` for any nonnegative `δ` bounded by every path
  residual capacity.  Its flow function is old flow plus `pathDelta`.
- [ ] Prove capacity by splitting on forward/reverse/non-path membership.
  Forward membership uses `δ ≤ c(u,v)-f(u,v)`; reverse membership subtracts a
  nonnegative amount; simplicity rules out both directions simultaneously.
- [ ] Prove skew-symmetry from the two skew laws.
- [ ] Prove internal conservation from the divergence formula and the endpoint
  equalities.
- [ ] Prove exact value:

```lean
theorem Flow.augmentBy_value :
  (φ.augmentBy p δ hδ hcap).value = φ.value + δ
```

- [ ] Define `Flow.augment` using the bottleneck and prove:

```lean
theorem Flow.augment_value :
  (φ.augment p).value = φ.value + p.bottleneck

theorem Flow.value_lt_augment :
  φ.value < (φ.augment p).value
```

## Task 6: Make the augmentation layer public and turn GREEN

**Files:**

- Modify: `CLRSLean/Chapter_26.lean`
- Modify: `literate.toml`
- Modify: `Tests/Chapter_26_Augmentation_Interface.lean`
- Modify: the new augmentation module docstring

- [ ] Import the new module from the Chapter 26 aggregator.
- [ ] Register the page in `literate.toml` with a partial Ford-Fulkerson title.
- [ ] Keep only the stable public names in the interface test.
- [ ] Run:

```bash
lake build CLRSLean.Chapter_26.Section_26_2_Ford_Fulkerson_Augmentation
lake env lean -DwarningAsError=true Tests/Chapter_26_Augmentation_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_26_Interface.lean
lake build CLRSLean.Chapter_26
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_26 Tests/Chapter_26_*.lean
python3 scripts/check_repository.py
git diff --check
```

- [ ] Independently review the public theorem statements and capacity proof.
- [ ] Commit:

```text
feat(ch26): add residual-path augmentation foundation
```

## Task 7: Extract a simple path from residual reachability

**Files:**

- Modify:
  `CLRSLean/Chapter_26/Section_26_2_Ford_Fulkerson_Augmentation.lean`
- Modify: `Tests/Chapter_26_Augmentation_Interface.lean`

- [ ] Use `List.exists_isChain_ne_nil_of_relationReflTransGen` to obtain a
  nonempty residual walk with the correct endpoints.
- [ ] Add a local generic duplicate decomposition lemma, following the
  repository's Chapter 24 cycle-removal pattern without importing Chapter 24.
- [ ] Erase one enclosed cycle while preserving `IsChain`, head, and last.
- [ ] Use well-founded induction on list length to obtain a `Nodup` walk.
- [ ] Package the result as `Flow.ResidualPath` and prove:

```lean
theorem Flow.hasAugmentingPath_iff_nonempty_augmentingPath :
  φ.hasAugmentingPath ↔ Nonempty (Flow.AugmentingPath φ)
```

- [ ] Prove strict augmentation contradicts maximality:

```lean
theorem Flow.not_maximal_of_augmentingPath ...
theorem Flow.not_maximal_of_hasAugmentingPath ...
```

## Task 8: Package Max-Flow Min-Cut equivalences

**Files:**

- Modify:
  `CLRSLean/Chapter_26/Section_26_6_MaxFlow_MinCut.lean`
- Modify: `Tests/Chapter_26_Augmentation_Interface.lean`
- Modify: Chapter 26 status prose only for the theorem groups now proved

- [ ] Import the augmentation module.
- [ ] Prove `Flow.maximal_iff_noAugmentingPath` by combining the existing
  `maximal_of_noAugmentingPath` direction with concrete strict augmentation.
- [ ] Refactor or expose the existing residual-reachable cut argument as
  `exists_cut_value_eq_of_noAugmentingPath`; do not assume the missing
  direction as a certificate.
- [ ] Package `maximal_iff_exists_cut_value_eq`, reusing the already proved
  `eq_cutCapacity_implies_maximal` direction.
- [ ] Run the full Task 6 verification matrix again.
- [ ] Independently review the new proof surface.
- [ ] Commit:

```text
feat(ch26): complete max-flow min-cut equivalence
```

## Success criteria

- A concrete simple residual path produces a feasible flow with strictly larger
  value.
- The proof supports anti-parallel capacities and never assumes arbitrary flow
  values are nonnegative.
- Residual reachability yields a concrete simple augmenting path without an
  unproved cycle-erasure assumption.
- Maximal flow, absence of an augmenting path, and equality with some cut
  capacity are connected by compiled theorems.
- No `sorry`, `admit`, or project axiom is added.
- BFS/Edmonds-Karp complexity, Lemma 26.7, and matching remain visibly separate
  later milestones.
