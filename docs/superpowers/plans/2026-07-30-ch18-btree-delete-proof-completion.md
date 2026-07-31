# Chapter 18.3 B-tree Deletion Proof Completion Plan

## Outcome

**Status:** Completed by `f3f61b4` for the structural deletion milestone. The task boxes below preserve the original execution plan; they are not current repository TODOs. That commit also completed same-depth preservation and root deletion height behavior. Exact deletion semantics was completed in a subsequent milestone; the 2026-07-31 minimum-key and logarithmic-height work then brought Chapter 18 to `134/134`.

> **For Codex:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task.

**Goal (historical):** Close every structural Chapter 18.3 deletion proof placeholder under mathematically correct contracts, add root contraction, restore the missing `splitChild` public wrappers, and pass the Chapter 18 and documentation gates without `sorry`, `admit`, or new axioms.

**Architecture (realized):** First correct `Occupancy` so an internal root has the standard two-child lower bound while a non-root keeps the `t`-child lower bound. Keep `composedDelete` as the raw node operation. `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Preservation.lean` provides the supporting preservation layer; the structural induction capstone is `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`, whose bundled theorem uses the generated `composedDelete.induct`. Project component theorems from that bundle, then expose `composedDeleteRoot := normalizeRoot ∘ composedDelete` with genuine `WellFormed`, subset, and height theorems.

**Tech Stack:** Lean 4, Mathlib, Lake, repository checker.

---

## Current verification gate

```sh
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion
for f in Tests/Chapter_18_*Interface.lean Tests/Chapter_18_Root_Occupancy.lean; do
  lake env lean -DwarningAsError=true "$f"
done
python3 scripts/check_repository.py
python3 scripts/check_progress_csv.py
```

---

## Task 1: Freeze the corrected contract with red tests

**Files:**

- Modify: `docs/superpowers/specs/2026-07-27-ch18-btree-delete-guard-design.md`
- Create: `Tests/Chapter_18_Deletion_Interface.lean`
- Create: `Tests/Chapter_18_Root_Occupancy.lean`

- [ ] Encode the `t = 3` valid internal-root/two-child regression and the corresponding
      non-root child-count distinction.
- [ ] Encode the non-root minimal-leaf counterexample to the old occupancy theorem.
- [ ] Encode the malformed empty-key-descendant counterexample to unconditional subset.
- [ ] Encode the valid one-separator root whose raw result needs contraction.
- [ ] Add `#check` expectations for `NodeWF`, `DeleteReady`, `RootDeleteResult`,
      `composedDelete_nonRoot_preserves`, `composedDelete_rootResult`,
      `normalizeRoot`, `composedDeleteRoot`, and `composedDeleteRoot_wellFormed`.
- [ ] Run `lake env lean Tests/Chapter_18_Deletion_Interface.lean` and record the expected
      unknown-constant failures before implementation.

## Task 2: Correct root-specific occupancy

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Invariant.lean`

- [ ] Give a non-empty internal root child lower bound `2`; keep non-root lower bound `t`.
- [ ] Preserve the leaf alternative and the existing upper bound.
- [ ] Update split/insert proofs affected by unfolding the refined definition.
- [ ] Update the non-root-to-root occupancy bridge to use `2 ≤ t`.
- [ ] Build model, insertion, and deletion modules and turn the root regression GREEN.

## Task 3: Restore the independent `splitChild` API

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Verify: `Tests/Chapter_18_Interface.lean`

- [ ] Add `splitChild_keys_perm_valid` for the real three-argument operation.
- [ ] Restore the 12 documented Valid/mem/search wrappers with honest parameters.
- [ ] Run the insertion file and Chapter 18 interface test.
- [ ] Complete independent spec-compliance and code-quality reviews.

## Task 4: Add invariant contracts and root normalization

**Files:**

- Create: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Invariant.lean`
- Modify: `CLRSLean/Chapter_18.lean`

- [ ] Define `NodeWF`, `DeleteReady`, `KeysSubset`, and `RootDeleteResult`.
- [ ] Define `normalizeRoot` and `composedDeleteRoot`.
- [ ] Prove basic projection lemmas and the non-root-to-root occupancy bridge.
- [ ] Prove normalization facts for ordinary roots, empty leaves, and one-child empty roots.
- [ ] Run the new interface test; definitions should be green while preservation theorems remain red.

## Task 5: Build the child, index, and repair packet layer

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Invariant.lean`
- Create: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Repair.lean`
- Import: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Rotation.lean`

- [ ] Prove child invariant projection and internal-node lookup existence.
- [ ] Prove guard-failure plus occupancy gives exactly `t - 1` keys.
- [ ] Prove sibling height/shape facts from `SameDepth`.
- [ ] Add the missing bundled `rotateLeft` preservation result.
- [ ] Bundle merge, borrow-left, and borrow-right results across all invariants, height,
      positive keys, and key membership.
- [ ] Compile `Invariant.lean` with zero placeholders.

## Task 6: Build parent reassembly packets

**Files:**

- Create: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Reassembly.lean`

- [ ] Prove the direct child-set packet.
- [ ] Prove predecessor separator replacement.
- [ ] Prove successor separator replacement.
- [ ] Prove adjacent-child rotation reassembly.
- [ ] Prove merge splice reassembly for left and right forms.
- [ ] Each packet must return every invariant, raw height, and key subset needed by the core.
- [ ] Compile `Reassembly.lean` with zero placeholders.

## Task 7: Prove the bundled raw deletion theorem

**Files:**

- Create supporting layer: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Preservation.lean`
- Create capstone: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean`

- [ ] Use the generated `composedDelete.induct` with a motive generalized over deletion key, tree, and root flag.
- [ ] Close the leaf case.
- [ ] Close predecessor, successor, and separator-merge cases.
- [ ] Close direct, borrow-left, borrow-right, merge-left, and merge-right descent cases.
- [ ] Eliminate well-formed-input lookup fallbacks by contradiction.
- [ ] Export `composedDelete_nonRoot_preserves` and `composedDelete_rootResult`.
- [ ] Compile the `ComposedPreservation.lean` capstone and inspect headline theorem axioms.

## Task 8: Replace component skeletons with projections

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Subset.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/SameDepthHeight.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Sorted.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ChildBounded.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Occupancy.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/WellFormed.lean`

- [ ] Delete all duplicate legacy induction skeletons and their 19 `sorry`s.
- [ ] Reintroduce component names as projections with corrected prerequisites.
- [ ] Prove root-normalized `composedDeleteRoot_wellFormed`; remove the false raw-root theorem name.
- [ ] Prove `composedDeleteRoot_keys_subset` and the at-most-one-level height result.
- [ ] Run both Chapter 18 interface tests.

## Task 9: Synchronize chapter and proof documentation

**Files:**

- Modify: `CLRSLean/Chapter_18.lean`
- Modify: `docs/chapters/chapter-18.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/proof-patterns/stuck-points-and-reusable-structures.md`

- [ ] Remove stale claims that raw `composedDelete` directly preserves root `WellFormed`.
- [ ] Document the raw/root-normalized API boundary and exact theorem contracts.
- [ ] Record that structural preservation and subset are complete.
- [ ] Record exact deletion membership semantics as a subsequently completed milestone, not as remaining work.
- [ ] Ensure every documented public name is checked by a Lean interface test.

## Task 10: Single-chapter/docs verification and review

**Files:**

- Verify all changed Lean and documentation files.

- [ ] Run the current single-chapter/docs verification gate shown above.
- [ ] Run `#print axioms` for both bundled preservation and normalized WellFormed theorems.
- [ ] Complete independent spec-compliance and code-quality reviews.
- [ ] Present branch integration choices without modifying unrelated user work.
