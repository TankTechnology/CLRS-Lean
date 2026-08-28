# Chapter 25 Attached Adjacency-Cost Implementation Plan

> **Execution rule:** implement locally, one task at a time, using RED/GREEN
> interface checks and small-file compilation.  Do not run a Chapter 25 or
> repository-wide build between local proof edits.

**Goal:** Replace the specification-only Chapter 25 flow budget with a
same-execution theorem: a support-indexed residual BFS selects a path, a
concrete alternating-path program updates the returned matching along that
path, and the accumulated RAM-model work is bounded by `O(V_f E_f)`.

**Implemented outcome (2026-08-28):** The closure uses a direct matching-state
run.  Every recursive state is already a proved `Matching`; its semantic flow
is definitionally `matchingToFlow` and is proved integral.  The support BFS
erases exactly to `residualBFS`, while the returned parent list is projected
to graph vertices by an explicit charged pass and fed to the concrete
erase/insert matching update.  Different valid augmenting-path choices need
not make the state sequence equal to the legacy `bfsFlowIter`, so the public
refinement is per-state (`flow = matchingToFlow matching`) rather than equality
to that legacy iteration.  The final execution proves a maximum matching, a
maximal integral attached flow, the exact component-sum bound, and
`work ≤ 20 * V_f * (E_f + 1)`.
The residual-support index is constructed once at the top level and threaded
through all recursive attempts.  The work field is an explicit textbook
unit-cost RAM counter, not a measurement of Lean evaluator time.

**Architecture:** Add a reusable finite-support adjacency and costed BFS layer
beside Chapter 24's existing semantic BFS.  Specialize it to the bipartite
matching network, prove exact state erasure, translate the exact BFS parent
path, update a concrete matching structurally, and run at most `|G.L|`
augmentations.  Keep the existing Chapter 25 flow iteration as a semantic
reference; do not represent its all-vertices scan as adjacency-list work.

**Tech stack:** Lean 4, Mathlib `Finset`/`List`/`Function.update` libraries,
Chapter 24 `BFSState` and residual-path API, Chapter 25 matching-flow and Berge
theorems, and the repository trust/audit scripts.

**Approved design:**
`docs/superpowers/specs/2026-08-28-ch25-costed-bipartite-flow-design.md`.

---

## Public contract

The final facade must expose declarations with these roles (names may change
only if Lean namespace conflicts force a documented rename):

```lean
#check CLRS.Chapter26.costedResidualBFS_state
#check CLRS.Chapter26.costedResidualBFS_work_le
#check CLRS.Matchings.matchingFlowResidualSupport_covers
#check CLRS.Matchings.matchingCostedBFS_state
#check CLRS.Matchings.augmentMatchingAlong_size
#check CLRS.Matchings.augmentMatchingAlong_work_le
#check CLRS.Matchings.costedMatchingRun_maximum
#check CLRS.Matchings.costedMatchingRun_work_le
#check CLRS.Matchings.flowMethod_finds_maximum_matching_with_attached_cost
```

The headline theorem must bundle the matching, semantic flow, augmentation
count, and work of one `costedMatchingRun G`; separate existential witnesses
or unrelated arithmetic fields do not satisfy the contract.

## Task 1: Freeze the missing interface in RED

**Files:**

- Create: `Tests/Chapter_25/CostedBipartiteFlow.lean`

- [ ] Import the future `FlowExecution.CostedRun` facade and add the nine
  `#check` declarations from the public contract.
- [ ] Add small `Fin`-vertex regression examples for adjacency construction,
  a graph with one augmenting edge, and a graph whose matching is already
  maximum.  Use `decide`/`rfl` where possible; do not add `native_decide`.
- [ ] Run:

  ```bash
  lake env lean Tests/Chapter_25/CostedBipartiteFlow.lean
  ```

  Expected RED result: the future facade or declarations are unknown.
- [ ] Commit the test contract separately:

  ```bash
  git add Tests/Chapter_25/CostedBipartiteFlow.lean
  git commit -m "test(ch25): specify attached flow-cost closure"
  ```

## Task 2: Build reusable support adjacency

**Files:**

- Create:
  `CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S4_ExecutableBFS/SupportAdjacency.lean`
- Create: `Tests/Chapter_24/SupportAdjacency.lean`

- [ ] Define a bucket representation and a costed builder over a duplicate-free
  support list:

  ```lean
  structure SupportAdjacency (V : Type*) [DecidableEq V] where
    bucket : V → Finset V

  structure SupportBuild (V : Type*) [DecidableEq V] where
    adjacency : SupportAdjacency V
    work : Nat

  def SupportAdjacency.insertArc
      (A : SupportAdjacency V) (e : V × V) : SupportAdjacency V

  def buildSupportAux : List (V × V) → SupportBuild V

  noncomputable def buildSupportAdjacency
      (support : Finset (V × V)) : SupportBuild V
  ```

  `insertArc` is one modeled indexed bucket update.  The builder increments
  `work` in the recursive branch that performs that update.
- [ ] Prove `mem_buildSupportAdjacency`:

  ```lean
  v ∈ (buildSupportAdjacency support).adjacency.bucket u ↔
    (u, v) ∈ support
  ```

- [ ] Prove the executed builder work and storage identities:

  ```lean
  (buildSupportAdjacency support).work = support.card
  ∑ u, ((buildSupportAdjacency support).adjacency.bucket u).card = support.card
  ```

- [ ] Prove the subset-sum lemma used by BFS: for `processed : Finset V`, the
  sum of processed bucket sizes is at most total storage.
- [ ] In `Tests/Chapter_24/SupportAdjacency.lean`, check membership, exact work,
  and total storage on a three-arc `Fin 4` support.
- [ ] Compile only the new module and focused test, then commit:

  ```bash
  lake env lean CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S4_ExecutableBFS/SupportAdjacency.lean
  lake env lean Tests/Chapter_24/SupportAdjacency.lean
  git add CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S4_ExecutableBFS/SupportAdjacency.lean Tests/Chapter_24/SupportAdjacency.lean
  git commit -m "feat(ch24): verify finite support adjacency buckets"
  ```

## Task 3: Specialize the matching-flow residual support

**Files:**

- Create:
  `CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/ResidualSupport.lean`
- Modify: `Tests/Chapter_25/CostedBipartiteFlow.lean`

- [ ] Define the forward and oriented support `Finset`s from source-to-left,
  embedded graph, and right-to-sink arcs:

  ```lean
  noncomputable def matchingFlowForwardSupport (G : BipartiteGraph V) :
      Finset ((V ⊕ Bool) × (V ⊕ Bool))

  noncomputable def matchingFlowResidualSupport (G : BipartiteGraph V) :
      Finset ((V ⊕ Bool) × (V ⊕ Bool))
  ```

- [ ] Prove the three forward families are pairwise disjoint and their maps
  injective.  Derive:

  ```lean
  (matchingFlowForwardSupport G).card = flowArcCount G
  (matchingFlowResidualSupport G).card = 2 * flowArcCount G
  ```

  If the doubled-support equality needs a no-self-loop lemma, prove that lemma
  explicitly rather than weakening the public result to a stipulated count.
- [ ] Prove a reusable generic flow lemma: a residual edge implies nonzero
  capacity in the forward or reverse direction.  Specialize `capFunc` to prove:

  ```lean
  theorem matchingFlowResidualSupport_covers (M : Matching V G) {u v} :
    Flow.residualEdge (matchingToFlow M) u v →
      (u, v) ∈ matchingFlowResidualSupport G
  ```

- [ ] Build `matchingFlowAdjacency G` with `buildSupportAdjacency` and prove
  bucket-filter equality with `residualAdj (matchingToFlow M) u`.
- [ ] Extend the RED test with concrete support-cardinality and coverage
  checks.  Compile this file and the focused test only.
- [ ] Commit Tasks 2–3 as the first implementation checkpoint if Task 2 was
  not already committed; otherwise commit Task 3 separately:

  ```bash
  git commit -am "feat(ch25): index matching-flow residual support"
  ```

## Task 4: Implement and erase the costed support BFS

**Files:**

- Create:
  `CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S4_ExecutableBFS/CostedSupportBFS.lean`
- Create: `Tests/Chapter_24/CostedSupportBFS.lean`

- [ ] Define a cost state containing the existing `BFSState`, a processed
  vertex set, and separate counters for vertex work, candidate scans, and
  discovery writes.  The total `work` is their sum.
- [ ] Define `costedBFSAdvance`, `costedBFSAux`, and `costedResidualBFS`.  One
  nonempty-queue step must:

  1. read exactly the popped vertex's bucket;
  2. test every candidate in that bucket against the residual predicate and
     visited set;
  3. perform the same queue/distance/parent update as `bfsStateAdvance`;
  4. add the executed scan and write counts.

- [ ] Parameterize the algorithm by a coverage hypothesis
  `residualEdge φ u v → v ∈ A.bucket u` and prove the filtered bucket equals
  `bfsNewNeighbors φ state u`.
- [ ] Prove one-step erasure, then fuel induction:

  ```lean
  theorem costedResidualBFS_state ... :
    (costedResidualBFS A φ cover).state = residualBFS φ
  ```

- [ ] Prove the processed-set invariant: popped vertices are fresh, processed
  remains a subset of `univ`, and its accumulated scan count is exactly the
  sum of its bucket sizes.
- [ ] Bound vertex work by `Fintype.card V`, scan work by adjacency storage,
  and writes by `Fintype.card V`.  Combine them into
  `costedResidualBFS_work_le` with explicit constants derived from the
  definition.
- [ ] Add a path-recovery counter that recursively traverses the returned
  `BFSParentPath`; prove its erased list is `BFSParentPath.vertices` and its
  work is linear in the returned path length.
- [ ] Test exact erasure and the work inequality on a small support graph.
  Compile only this module and test, then commit:

  ```bash
  git commit -am "feat(ch24): verify costed support-indexed residual BFS"
  ```

## Task 5: Tie the exact BFS parent path to an alternating path

**Files:**

- Create:
  `CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/CostedBFS.lean`
- Modify: `Tests/Chapter_25/CostedBipartiteFlow.lean`

- [ ] Define `matchingCostedBFS G M` using the support and coverage theorem.
  Prove `matchingCostedBFS_state` by the generic erasure theorem and specialize
  the generic work bound using support cardinality.
- [ ] Branch on the returned sink distance, not on a detached existential
  proposition.  `none` must imply no residual augmenting path by the erased
  state theorem.
- [ ] In the `some d` branch, recover the exact parent path from that state and
  use `translation_inner` to produce an `IsAugmentingPath`.  Preserve a theorem
  stating that the graph path came from this exact parent-path vertex list.
- [ ] Include parent-path recovery work in the returned attempt record and
  prove the complete search-plus-recovery bound.
- [ ] Test both the no-path and one-edge path branches.  Compile only the new
  file and focused test.

## Task 6: Implement the attached alternating-path update

**Files:**

- Create:
  `CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/MatchingAugment.lean`
- Modify: `Tests/Chapter_25/CostedBipartiteFlow.lean`

- [ ] Define explicit `insertAugmentingEdge` and `swapAugmentingEdge`
  constructors using `Finset.insert` and `Finset.erase`.  Prove their matching
  invariants and exact sizes directly; do not select the witnesses of
  `exists_augment_single` or `exists_swap`.
- [ ] Define `MatchingAugmentRun` and a well-founded structural recursion over
  an `IsAugmentingPath`:

  ```lean
  structure MatchingAugmentRun (G) (M : Matching V G) where
    matching : Matching V G
    work : Nat

  noncomputable def augmentMatchingAlong
      (M : Matching V G) (p : List V) (hp : IsAugmentingPath G M p) :
      MatchingAugmentRun G M
  ```

  The two-vertex case performs one insert.  The longer case performs the
  leading erase/insert swap and recursively augments the strictly shorter
  tail.
- [ ] Prove from the recursion, not from an existential wrapper:

  ```lean
  augmentMatchingAlong_size
  augmentMatchingAlong_work_eq
  augmentMatchingAlong_work_le
  ```

  with final size `M.size + 1` and work bounded by the path length.
- [ ] Prove that the update uses exactly the forward and backward alternating
  edges of the BFS-derived path.  Use this to refine `matchingToFlow` before
  and after the update to semantic augmentation along the parent path.  Keep
  this proof in a separate final section so the executable recursion remains
  fast to elaborate.
- [ ] Add single-edge and three-edge alternating-path tests.  Compile only the
  update module and focused test, then commit:

  ```bash
  git commit -am "feat(ch25): verify attached alternating-path updates"
  ```

## Task 7: Assemble the same-execution costed run

**Files:**

- Create:
  `CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/CostedRun.lean`
- Modify:
  `CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution.lean`
- Modify: `Tests/Chapter_25/CostedBipartiteFlow.lean`

- [ ] Define a run record containing the concrete matching, its definitional
  semantic flow, augmentation count, attempt count, preprocessing work, BFS
  work, path-recovery work, update work, and total work.
- [ ] Define the runner by recursion on remaining fuel with invariant
  `M.size + fuel = G.L.card`.  Start with the empty matching and
  `fuel = G.L.card`.
- [ ] In each branch use the actual `matchingCostedBFS` result.  On `none`,
  return immediately.  On `some`, pass that exact alternating path to
  `augmentMatchingAlong` and recurse with one less fuel.
- [ ] Prove the returned matching is maximum:

  - the no-path branch uses residual translation plus Berge;
  - the zero-fuel branch uses `M.size = G.L.card` and the matching-size upper
    bound;
  - the active branch follows the recursive theorem after exact size growth.

- [ ] Prove `augmentations ≤ G.L.card` and that the flow field is exactly
  `matchingToFlow run.matching`.
- [ ] Sum the executed component counters.  Establish the primary exact bound:

  ```text
  run.work ≤ supportBuildWork G +
    G.L.card * (bfsBound G + pathBound G + updateBound G)
  ```

- [ ] Derive a closed natural-number product bound using
  `flowVertexCount G = Fintype.card V + 2`,
  `flowArcCount G = G.L.card + G.E.card + G.R.card`, and partition coverage.
  Handle `flowArcCount G = 0` separately, then publish
  `costedMatchingRun_work_le` and the bundled headline theorem
  `flowMethod_finds_maximum_matching_with_attached_cost`.
- [ ] Import `CostedRun` from the `FlowExecution.lean` facade and make the
  entire RED contract GREEN.
- [ ] Compile `CostedRun.lean` and `Tests/Chapter_25/CostedBipartiteFlow.lean`,
  then commit:

  ```bash
  git commit -am "feat(ch25): close matching flow with attached O(VE) work"
  ```

## Task 8: Publish, audit, and integrate

**Files:**

- Modify:
  `CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_25.lean`
- Modify: `Tests/Chapter_25/BFSBipartiteFlow.lean`
- Modify: `Tests/Trust/Chapter_25.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/audits/2026-08-28-whole-book-proof-gap-audit.md`
- Modify generated reader/progress artifacts only through their repository
  generators.

- [ ] Replace any public wording that describes `augmentationAttemptBudget`
  as the cost of the old all-vertices `residualBFS`.  Preserve it only as a
  specification budget if downstream proofs still need the arithmetic lemma.
- [ ] Add the attached-cost theorem to the section and chapter reader surface,
  focused interface checks, and the trust audit.
- [ ] Run the integration checkpoint once:

  ```bash
  lake env lean Tests/Chapter_24/SupportAdjacency.lean
  lake env lean Tests/Chapter_24/CostedSupportBFS.lean
  lake env lean Tests/Chapter_25/CostedBipartiteFlow.lean
  lake env lean Tests/Chapter_25/BFSBipartiteFlow.lean
  lake env lean Tests/Trust/Chapter_25.lean
  lake build CLRSLean.FourthEdition.Chapter_25
  ```

- [ ] Run the repository's progress, trust, documentation, and whitespace
  gates discovered from `Makefile`, CI workflows, and `scripts/`; do not guess
  command names.
- [ ] Search the touched proof surface for forbidden placeholders and inspect
  every match:

  ```bash
  rg -n "\bsorry\b|\badmit\b|\baxiom\b|native_decide" \
    CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S4_ExecutableBFS \
    CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching \
    Tests/Chapter_24 Tests/Chapter_25 Tests/Trust/Chapter_25.lean
  git diff --check main...HEAD
  ```

- [ ] Request semantic review of the exact committed diff.  Fix every
  Important or merge-blocking finding and rerun its narrow reproducer.
- [ ] Rebase or merge the verified branch into local `main`, rerun the final
  authoritative gates on `main`, push `main`, and update issue #339 with exact
  theorem names, commit hashes, and verification output.  Close #339 only if
  the attached execution theorem is present and audited.
