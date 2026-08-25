# Stuck-point case retrospective (as of 2026-07-24)

> This article is a point-in-time retrospective of the commit history and proof-attack paths, not a current to-do list.
> "Later results" are recorded as a follow-up based on the repository state as of 2026-07-31.

Based on the commit timeline, commit messages, and the project ledger in effect from 2026-06-23 to 2026-07-24,
this article organizes seven representative proof stuck-point cases. The time spans and commit counts are approximate observations at that point;
"quiet periods" may also include parallel work on other chapters, so commit order is treated here only as evidence,
not interpreted as a single cause or as exact effort.

## Seven representative cases

### Case 1: the four preservation theorems for `splitChild` in Chapter 18.1

- **Span**: 2026-07-06 to 2026-07-08, about two and a half days and roughly twenty commits.
- **Commit observations**: `6da958f` attempted to break down `splitChild` with `match`, and about seven minutes later
  `65a6d09` restored a clean state; the commit message called out the interface obstacles posed by `Sublist.subset` and
  `List.get_mem`. The detailed scratch notes remain recoverable from Git history.
- **Main obstacles at the time**: the commit messages together with the later rewrites show that the `let` bindings in `splitChild`
  interfered with `rw`, `dsimp`, and typeclass search; the old definitional shape of `SameDepth`
  was also awkward to destruct.
- **Path to closing**: `SameDepth` was changed to an inductive definition, `splitChild` was reshaped to a `let`-free
  form, and paving lemmas such as `sameDepth_take`, `sameDepth_drop`, and `pairwise_get_mono`
  then completed the depth, occupancy, sortedness, and sub-interval bounds respectively.
- **Module and results**:
  `splitChild_preserves_sameDepth`, `splitChild_preserves_occupancy`,
  `splitChild_preserves_sorted`, `splitChild_preserves_childBounded`, and
  `splitChild_preserves_wellFormed` in `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`.

### Case 2: the `WithTop ℝ` coercion in Chapter 25 Floyd–Warshall

- **Span**: 2026-07-13 to 2026-07-23, about ten days.
- **Commit observations**: `d94d83b` records that "not all proofs compile", and `dc50d37` records
  that about fifteen errors remained; about a week later the infrastructure was re-laid, and the core proof was finished within two days.
  The retrospective later also specifically corrected the assessment that `AddRightMono` was missing.
- **Main obstacles at the time**: the official retrospective records that the implicit and explicit coercions of `WithTop ℝ`
  made `rw` hard to match, made `subst` inapplicable to the relevant equations, and that over-unfolding produced long branches.
- **Path to closing**: name the intermediate path conditions with `Through`; use
  `Option.ne_none_iff_exists'` to return to a real-number witness; use
  `revert`, `induction`, and `intro` to rearrange the induction variables; diagnose the coercion in a minimal standalone file.
  This sequence appeared together with the closing of the proof, but the commit timeline alone cannot attribute it to the
  isolated effect of any single trick.
- **Module and results**:
  `Through`, `floydWarshall_le_walk`, and `floydWarshall_isShortestDist` in `CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean`; see
  [`ch25-proof-retrospective.md`](ch25-proof-retrospective.md) for the detailed retrospective.

### Case 3: the cross-layer DFS invariants of Kosaraju SCC in Chapter 22

- **Span**: 2026-07-05 to 2026-07-10, about five days and roughly thirty substantive commits, followed by a further
  batch of refactoring commits.
- **Commit observations**: `d112984` records that five placeholders remained, and `b2452d6` opened a new bridge file and recorded
  that the `v ≠ u` branch was still unfinished; fuel induction then completed
  `dfsVisit_white_to_nonwhite_disc_ge_time`, and `79791d0` fixed the bridge and completed
  `scc_finish_time_order`. Along the way, the return packet of `exists_discovery_state` repeatedly gained
  nonwhite, black-finish, `f`-preservation, and suffix fields.
- **Main obstacles at the time**: the fold accumulator of DFS spans multiple layers of recursion, and the intermediate-state invariants could not
  be obtained directly by structural induction on the outer layer; the finishing stage also needed to align the strict and
  non-strict relations used by merge sort.
- **Path to closing**: move the cross-layer properties to
  `CLRSLean/Chapter_22/Section_22_3_DFS/S3_Bridge.lean`, use fuel induction to penetrate
  `dfsVisit`, and use `dfsVisit_fold_blackens_loc_prefix` to handle the fold prefix.
- **Module and results**: besides the bridge module,
  `CLRSLean/Chapter_22/Section_22_3_DFS/S4_SCC.lean` provides
  `exists_discovery_state`, and
  `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean`
  provides `scc_finish_time_order`.

### Case 4: the representation change for red-black tree deletion in Chapter 13/14

- **Span**: 2026-06-24 to 2026-07-20, about twenty-six days.
- **Commit observations**: the 2026-07-11 commit message left the fully executable deletion repair loop for later;
  the next day introduced `baldL`, `baldR`, and the weakened invariant `NoRedRed2`; on 2026-07-13 the
  executable deletion and membership were completed, and on 2026-07-20 `baldL_shape`,
  `splitMin_invariant`, and `del_invariant` filled in shape preservation, with Chapter 14 mirroring afterward.
- **Main obstacles at the time**: the commit sequence shows that the imperative double-black loop was hard to compose directly into the current
  functional tree model.
- **Path to closing**: switch to an Okasaki/Kahrs-style functional deletion, let `baldL` and
  `baldR` absorb one level of black-height deficit, use `NoRedRed2` to accommodate localized temporary weakening, and then compose
  via `splitMin` and `join`. Completing membership first and shape preservation afterward is a two-phase order
  directly observable in this history.
- **Module and results**:
  `baldL_shape`, `baldR_shape`, `splitMin_invariant`, and `del_invariant` in `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`.

### Case 5: the semantic invariants of recursive vEB deletion in Chapter 20

- **Span**: 2026-07-13 to 2026-07-15, three days in total.
- **Commit observations**: `ed68dda` records four deferred branches and notes the need for
  `WellFormed`; on the same day a design document, a plan document, and interface tests appeared, and all deletion
  proofs were subsequently completed. The documents also identified that when the detached-minimum clause is missing, the unconditional deletion theorem does not hold.
- **Main obstacles at the time**: without representation invariants, the summary and cached min/max branches could not
  use a sufficiently strong recursion hypothesis.
- **Path to closing**: introduce `MinCorrect`, `MaxCorrect`, and `WellFormed`, and in
  `delete_correct` induct simultaneously on "invariant preservation" and the `Finset.erase` semantics. The later
  insert proof also exposed an implementation issue where repeated insertion loses the detached minimum.
- **Module and materials**:
  `delete_correct`, `delete_wellFormed`, and `delete_toFinset` in
  `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`. The original design and
  implementation-plan snapshots remain recoverable from Git history.

### Case 6: the discrete-to-continuous bridge for the Chapter 4 master theorem

- **Span**: 2026-06-24 to 2026-07-06, about twelve days.
- **Commit observations**: the message of `524fb76` states that three cases were completed, and `b009222` on the same day
  clarified that Chapter 4 and Chapter 5 were still partial results, with the actual boundary being exact powers;
  the next day transfer-bridge and wrapper commits appeared in succession, and on 2026-07-06 the regularity bridge for case 3
  was closed.
- **Main obstacles at the time**: an explicit asymptotic equivalence was needed between the discrete scale and the textbook real-exponent scale;
  case 3 also had to connect the CLRS regularity condition to tail-term domination.
- **Path to closing**: layer and compose
  `criticalPowerScale_isBigTheta_realLogScale`, `isBigTheta_trans`, and
  `Case3Regularity`. The commit order supports the description that "bridge layers were filled in step by step", but it does not support
  interpreting every wrapper as an indispensable causal step.
- **Module and results**:
  `criticalPowerScale_isBigTheta_realLogScale` and `Case3Regularity` in `CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean`.

### Case 7: the well-formedness of `composedDelete` in Chapter 18.3

- **Span**: 2026-06-25 to 2026-07-24, about thirty days, the longest attack record in this time window.
- **Commit observations**: on 2026-07-12 partial results were obtained for leaf removal and internal merge-recurse,
  and the next day a version of the termination problem was resolved; on 2026-07-20 the auxiliary lemmas were redone,
  and `22ffcee` established the four-component framework on 2026-07-24. At that time
  `composedDelete_key_bound_lo` was still a placeholder.
- **Main obstacles at the time**: on one hand, the merge branch does not exhibit a simple structural decrease; on the other hand,
  `WellFormed` simultaneously bundles `SameDepth`, `Sorted`, `ChildBounded`, and
  `Occupancy`, so a monolithic goal is hard to maintain.
- **Partial progress as of the cutoff**: `heightOf_mergeNodes_eq_max` supports the height-based
  termination argument; the four components each advanced, reusing the occupancy and child-bounded
  infrastructure from the insertion side; after changing the dependent `if` to an ordinary condition, `rw [composedDelete]` unfolded more easily.
  The remaining problems at the time centered on the child-bounded and key-bound transfer of the merge.
- **Module**:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion.lean`, along with the deletion
  submodules split out later, such as `ComposedPreservation`, `Exact`, `WellFormed`, and `SameDepthHeight`. See
  `docs/research/afp-btree-deletion-architecture-2026-07-27.md` for a later comparison of the AFP B-tree deletion architecture.

**Later results (as of 2026-07-31)**: the Chapter 18 search, insertion, structural deletion,
exact deletion, and height closure loops are all complete, with current progress at `134/134`. Shape preservation is consolidated by
`composedDelete_packet`, exact semantics are closed by `composedDelete_keyBag` and
`composedDeleteRoot_correct`, and the height result is given by
`wellFormed_height_log_bound`. This case therefore describes the
historical stuck point of 2026-07-24, not a current open problem.

## Appendix: a process collision — duplicate parallel PRs for Chapter 14

On 2026-07-11, the same work was redundantly implemented by parallel agents, with PR #8 and #15 and PR #16 and #17
overlapping respectively, followed by two "reconcile status after main merge" fixes.
worktree isolation, the parallel-agent runbook, and the QA agent followed shortly after on the timeline; this indicates
a clear association between the collision and the process hardening, but the existing records are not enough to assert that it was the sole
cause of these process changes.

## Five types of stuck points as of 2026-07-24

| Type | Representative case at the time | Reusable handling approach at the time |
|---|---|---|
| coercion / type layer | `WithTop ℝ` in Chapter 25 | avoid fragile `rw` with `simpa`, name intermediate terms with `set`, diagnose the coercion with a minimal repro |
| representation design | the functional deletion in Chapter 13/14, `WellFormed` in Chapter 20, and the general-size Strassen that was still deferred then | switch to a proof-friendly equivalent representation, separate the specification layer from the implementation layer, and explicitly register the lower-level refinement boundaries |
| insufficient induction strength | the double fuel in Chapter 9, the bundled theorems in Chapter 20, the fuel bridging in Chapter 22 | strengthen the induction proposition, bundle invariants together with the semantics, or make the recursion explicitly fuel-based |
| large goals hard to maintain as a whole | the scale bridge in Chapter 4, the four-component invariant in Chapter 18, Kruskal in Chapter 23 | split into components, bridge in layers, then consolidate with small wrappers |
| substantive gaps at the math layer | the expected-value identities in Chapter 7 at the time, the Chapter 5.4 logarithmic bound, general floor/ceiling recurrences | not all broken through in that snapshot; first freeze the exact theorem boundary, then fill in the mathematical bridges |

**Later results (as of 2026-07-31)**: the Chapter 7 expected-value bridge
`sum_compared_prob_eq_expectedComparisons` and the `Θ(n log n)` result
`expectedComparisons_isBigTheta_nlogn` are complete and can no longer be listed as open mathematical gaps.
According to the current progress ledger, the partial chapters are exactly **19, 26, 27, 33**; this current list should not be inferred backwards from
the historical examples in the table above.

## Rhythm signals as of 2026-07-24

In the commit timelines of cases 1, 2, and 5, an approximate sequence is visible:

**wip/partial commit → a low-density period → design, plan, or attack notes appear → followed by intensive closing.**

This is an associative signal worth using in project management: writing the goal, representation invariants, and interfaces into documents after getting stuck
often co-occurs with the later closing of proofs. However, the sample is small, and the low-density periods may have been advancing other work,
so it cannot prove that the documentation effort alone caused the closing. In contrast, in case 6 the "complete" and
"clarify partial" commits sit adjacent on the same day — a commit signal that should trigger a scope review, not a causal judgment about the authors' motivation
or the quality of the proofs.

## Interpretation boundaries

- This article preserves the commit and proof-path observations as of 2026-07-24 and does not take on the role of the
  current-state ledger.
- Deferred items are often deliberately deferred RAM, array, or pointer refinements; the deferred label alone cannot be used
  to conclude that something was once "stuck".
- The time interval between commits is not equal to the effort invested, and the ordering of representation adjustments versus proof completion does not automatically
  constitute a causal proof.
