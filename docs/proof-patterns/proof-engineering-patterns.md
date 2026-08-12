# CLRS-Lean Proof-Engineering Patterns

This document collects only the proof-engineering structures distilled from stuck-case postmortems that still have independent reuse value today. It complements
[geometric-proof-patterns](./geometric-proof-patterns.md) and
the [CLRS-Lean playbook](./clrs-lean-playbook.md): it does not repeat the former's
proof shapes such as Boundary, Exchange, Fiber, and Interval, nor the latter's general
tactic cheat sheet and chapter-advancement plan. Generic loop-invariant templates,
asymptotic-bridging stacks, and geometric atlas entries are therefore not given their
own patterns in this catalog.

## 1. Proving fold preservation field by field

**Structure**: when a record state is threaded through a list fold, first fix a precondition on the state, then prove, for each field,
separately, that the single step and the fold each preserve the invariant. The proofs share
`induction l generalizing s`, branch case analysis, and the `simp` skeleton, replacing only the field projection and the local
preservation lemma.

**Current instances**:
`dfsVisit_fold_preserves_d_of_black`,
`dfsVisit_fold_preserves_f_of_black`,
`dfsVisit_fold_preserves_d_of_not_white`, and
`dfsVisit_fold_preserves_f_of_not_white` in
`CLRSLean/Chapter_22/Section_22_3_DFS.lean`; the corresponding results for the parent field live in
`CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals.lean`.

**Usage guidelines**: when the state-update function changes only a few fields while later proofs query the untouched fields frequently,
prefer to build a field-level API. Once the field set is large and the proof skeleton is stable, consider generating a template; before confirming at least
two independent consumers, do not promote it into a heavyweight framework.

## 2. Enumerated families of relation lemmas

**Structure**: for an update operation, systematically cover the combinations among `x = y`, `x ≠ y`, `mem`, `not_mem`,
boolean queries, and proposition queries. The core semantic theorem is proved only once; the remaining results are assembled by symmetry,
rewriting, or one-line forwarding into a searchable interface family.

**Current instances**:
`delete_mem_iff`, `delete_mem_iff_ne`, `delete_search_iff`,
`delete_search_iff_ne`, `delete_search_of_mem_ne`, and
`delete_search_false_of_not_mem` in `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean`. The insertion module in the same chapter provides
`splitChild` and `insert` with a same-shaped membership/search interface.

**Usage guidelines**: once a tree's insert, delete, split, and join serve both boolean queries and
`Prop` specifications, first write out the relation matrix, choose one or two core iff's as the source of facts, then generate or forward
the remaining named theorems. This avoids downstream proofs repeatedly unfolding the implementation definitions.

## 3. Component decomposition of composite invariants

**Structure**: split a composite well-formedness condition into components that can be preserved independently; for each component, build local repair,
recursive-call, and recomposition lemmas, and package them together at the end. The component boundaries should align with the hypotheses the actual recursive branches need,
rather than jamming every condition into a single indecomposable predicate for the sake of a superficially short statement.

**Current instances**: Chapter 18's B-tree deletion hands `SameDepth`, `Sorted`,
`ChildBounded`, `Occupancy` to
`composedDelete_sameDepth_height`, `composedDelete_sorted`,
`composedDelete_childBounded`, `composedDelete_occupancy`, which are then aggregated by
`composedDelete_packet` in
`CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`.

Red-black trees must separate shape from ordering:

```text
RedBlackShape = RootBlack ∧ NoRedRed ∧ BalancedBlackHeight
```

The `BST` ordering is an independent precondition or invariant; it does not belong to `RedBlackShape`. The relevant definitions live in
`CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`.

**Usage guidelines**: if a recursive branch consumes only part of a composite invariant, expose the component lemma;
only the public entry point and the final correctness theorem should repackage the full condition.

## 4. Bundled induction of invariants and semantics

**Structure**: the inductive conclusion of a recursive theorem simultaneously returns
`PreservesInvariant ∧ RefinesToSpec`. After a recursive call, the preservation projection justifies subsequent caching,
summaries, or local repairs, while the semantic projection discharges the final specification equality; the two are not the result of two separate
traversals.

**Current instances**:
`delete_correct` in `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean` gives both `WellFormed` preservation and the `toFinset = Finset.erase`
semantics, with `delete_wellFormed` and `delete_toFinset` as its projections. Chapter 18's
`composedDelete_packet` also returns several structural components at once; the exact multiset semantics is subsequently attached by
`composedDelete_keyBag` in
`CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean`.

**Usage guidelines**: for data structures with caches, summaries, or redundant fields, if the recursive branches of the semantic proof need
the "recursive result is still well-formed" hypothesis, strengthen the inductive conclusion directly; do not finish a single semantic theorem and then duplicate the entire
induction to retrofit the preservation property.

## 5. Fuel-ized recursion and dual-fuel strengthened induction

**Structure**: explicit fuel turns recursion depth into an ordinary natural-number induction parameter; when the algorithm also has a
recursive sub-procedure inside, the induction proposition quantifies both the outer fuel and the inner fuel, keeping the "current input length
does not exceed either fuel" hypothesis. The real strengthening is that the induction hypothesis applies to any sufficiently large fuel, rather than
mechanically setting the two parameters to the same length.

**Current instances**:
`dfsVisit_white_to_nonwhite_disc_ge_time` in
`CLRSLean/Chapter_22/Section_22_3_DFS/S3_Bridge.lean` uses fuel to thread through the DFS;
`recursiveMedianOfMediansPivotFuel?` and `selectCostFuel` in
`CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean` express the recursion budgets of the pivot
and the selector respectively, and the dual-fuel strengthening ultimately supports the public result
`recursiveMedianOfMediansComparisonCost_linear_bound`.

**Usage guidelines**: with non-structural recursion, nested recursion, or when the same input is decreased through different sub-procedures,
first ask which recursion budgets need to vary independently in the induction hypothesis. Fuel does not replace the termination fact;
the public wrapper should still choose sufficient fuel and prove that it agrees with the fuel-free specification.

## 6. Weakened invariants and deficit absorption

**Structure**: when a local deletion or repair temporarily breaks a strong invariant, define a weakened predicate that relaxes only one clearly identified position
and lets the deficit propagate toward the parent level; the rebalancer absorbs one layer of deficit at a time and finally restores the strong invariant at the root.
The scope of the weakening and the recovery point must be written into the interface; a vague "almost well-formed" notion is not an acceptable substitute.

**Current instances**:
`NoRedRed2` in `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`
allows a local red-red conflict to be handled by recoloring the root, `baldL` and `baldR` absorb the left and right black-height deficits,
and `baldL_shape`, `baldR_shape`, `del_invariant` connect the local repairs to the final shape.

**Usage guidelines**: in deletions on balanced trees or heaps, if requiring the full invariant at every level makes the composition fail,
look for a deficit that can be repaid in a single step and prove that the propagation is at most one level. Do not weaken several
mutually unrelated properties at once, or the final restoration theorem turns back into a single monolithic goal.

## 7. Wrapping induction conditions in predicates

**Structure**: name a long, repeatedly occurring induction side-condition as a predicate and provide base, step,
monotonicity, and endpoint lemmas for it. The induction proposition is then stated around a stable concept rather than carrying a volatile unfolded form.

**Current instances**:
`Through S i j p` in `CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean`
states that the intermediate vertices of path `p` are restricted to the set `S`; it lets Floyd–Warshall's vertex-by-vertex induction
connect `floydWarshall_le_walk` directly to `floydWarshall_isShortestDist`.

**Usage guidelines**: in graph paths, restricted reachability, or staged dynamic programming, if the same side-condition appears in
more than three theorem signatures, name it first. The predicate should expose exactly the constructor and eliminator API the induction needs;
do not merely give a complex expression a new name and still unfold it fully in every proof.

## 8. Choosing tactics according to definition shape

**Structure**: when `rw`, `simp`, or the induction principle keeps failing to match, first inspect the shape of the expressions the definition generates,
then decide whether to change the tactic or the definition. The goal is for the definition to have a stable unfolded form and a usable elimination principle,
rather than relying on fragile simplification coincidences.

**Current instances**:

- `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean` makes `SameDepth` an
  inductive definition and gives `splitChild` a `let`-free shape that is easy to rewrite; its interface is wrapped by
  preservation theorems such as `splitChild_preserves_sameDepth`.
- The `composedDelete` of the Chapter 18 deletion uses non-dependent conditions, which makes it easy to
  unfold after a branch is selected; later proofs use it preferentially through `composedDelete_packet` and the component projections.
- Chapter 25's retrospective notes show that coercion goals often fit `simpa` better, or benefit from first pinning the
  intermediate term with `set`; when the order of induction variables needs to change, `revert`, `induction`, `intro`
  are more stable than forcing `generalizing` on the original goal.

**Usage guidelines**: first build a minimal reproduction and inspect the actual goal; adjust the definition only when multiple downstream proofs are blocked by the same
shape. After adjusting the definition, make named theorems the long-term interface, so that consumers do not again
rely on internal unfolding details.
