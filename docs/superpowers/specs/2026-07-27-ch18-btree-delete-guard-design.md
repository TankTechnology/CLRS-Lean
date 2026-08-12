# Ch18.3 `composedDelete` proof-closure design (2026-07-30 revision)

> **Status: complete.** This document records the structural-preservation design from 2026-07-27 to 2026-07-30. The structural preservation and deletion-height closure was completed in commit `f3f61b4`; exact deletion semantics were completed afterward, and on 2026-07-31 the whole chapter's minimum key count and logarithmic height bound were completed. Current progress is `134/134`.

## Design goals (historical)

At the design stage, the goal of this document was to close all proof placeholders around the Chapter 18.3 node-level B-tree deletion implementation while maintaining the following boundaries:

- Do not weaken `Sorted`, `ChildBounded`, `Occupancy`, `SameDepth`, or `WellFormed`;
- Do not replace the algorithm with an identity function or a list deletion at the canonical layer;
- The raw node deletion still uses the already-implemented CLRS pre-repair branches;
- The public root deletion adds the root contraction required by CLRS;
- The 2026-07-30 structural milestone proves only the structural invariants, raw height preservation, and the resulting key subset; it does not disguise the exact deletion semantics (unproven at that time) as complete. The exact semantics were later closed out separately.

## Five contract/model errors confirmed at the design stage

The 19 `sorry`s in the design starting point could not be filled in as-is at the time, because the outer theorems contained four kinds of false propositions or missing hypotheses, and the base `Occupancy` definition omitted a root-node special case. These 19 gaps have been closed by `f3f61b4`; the five items below are kept as counterexample evidence for the contract corrections, not as outstanding items in the current repository.

### 1. The unconditional key subset is false

`maxKey` / `minKey` are total functions on any `BTree`; reading along an empty-key descendant returns the default values of `getLast!` / `head!`. For a malformed tree that does not satisfy occupancy, case 1a/1b can therefore write a `0` that is not present in the input into the parent separator key.

Therefore `keysOf_composedDelete_subset` cannot hold unconditionally for arbitrary trees. The proof must carry `AllKeysPos`, or derive it from the full `Occupancy` bundle.

### 2. Non-root occupancy requires a deletion-entry readiness condition

For `t = 2` and the non-root leaf `node [1] []`, the input satisfies `Occupancy 2 false`, but after directly deleting `1` it has only `0` keys. The parent's pre-repair guard does not cover the scenario of "directly calling this non-root node".

The correct entry condition is:

```lean
def DeleteReady (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  isRoot = true ∨ t ≤ numKeys tr
```

All recursive calls satisfy the right disjunct: a direct descent is given by the guard, the recipient has at least `t` keys after a borrow, and `2 * t - 1` keys after a merge; the top-level root call satisfies the left disjunct.

### 3. The occupancy proof also requires the same-depth condition

`ChildBounded + Occupancy` alone still allows adjacent siblings where one is a leaf and the other is an internal node. Executing a borrow on such an input would move a grandchild node into the leaf recipient, producing an illegal number of children. The occupancy preservation of rotation already depends on the siblings having equal depth, so `SameDepth` is a mathematical hypothesis, not a proof convenience.

### 4. Raw root deletion does not preserve the existing `WellFormed`

For `t = 2`:

```lean
node [5] [node [1] [], node [9] []]
```

is `WellFormed`. raw `composedDelete 2 5` yields:

```lean
node [] [node [1, 9] []]
```

This is exactly the transient empty root of the CLRS deletion, but it does not satisfy this project's `Occupancy 2 true`: a zero-key root is only allowed when it also has no children. Therefore the old `WellFormed t tr → WellFormed t (composedDelete t x tr)` is false, and root contraction must be added.

### 5. The children lower bound of an interior root cannot reuse the non-root `t`

The original `Occupancy` special-cased only the root's key lower bound, yet uniformly required all non-leaf nodes to have at least `t` children. With `t > 2`, that definition wrongly rejects a standard B-tree root. For example, when `t = 3`, an interior root with one key and two minimal leaf children is legal; and after a deletion merges a three-child root into a two-child root, the algorithm's result is still legal.

The corrected children lower bound is:

```lean
let childLower := if isRoot then 2 else minDegree
children.isEmpty ∨
  (childLower ≤ children.length ∧ children.length ≤ 2 * minDegree)
```

Leaves are still allowed through by the `children.isEmpty` branch, non-roots still require at least `t` children, and the transient `node [] [child]` still does not belong to ordinary root occupancy and must be contracted by `normalizeRoot`. This correction does not weaken the CLRS invariant; it restores the lower bound that is unique to the root node in the standard definition.

## Algorithm semantics retained and implemented

raw `composedDelete` retains the current implementation:

- Leaf: `sortedRemove`;
- Separator hit:
  - Left child has at least `t` keys: replace with the predecessor `maxKey` and recursively delete the predecessor;
  - Otherwise the right child has at least `t` keys: replace with the successor `minKey` and recursively delete the successor;
  - Both sides are minimal: merge and then recurse;
- Ordinary descent:
  - Child has at least `t` keys: descend directly;
  - Otherwise prefer to rotate from a sibling that can lend;
  - When no sibling can lend, merge and then descend.

The raw function remains total on any `BTree`; the proof rules out the lookup-fallback branches on well-formed inputs and does not rely on the bogus invariants of those fallbacks.

## Structural preservation contract (implemented)

### Input bundle

```lean
def NodeWF (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  Sorted tr ∧
  ChildBounded tr ∧
  Occupancy t isRoot tr ∧
  SameDepth tr

def KeysSubset (after before : BTree) : Prop :=
  ∀ k, k ∈ keysOf after → k ∈ keysOf before
```

### Transient output of the raw root

```lean
def RootDeleteResult (t : Nat) (tr : BTree) : Prop :=
  Sorted tr ∧
  ChildBounded tr ∧
  SameDepth tr ∧
  (Occupancy t true tr ∨
    ∃ child, tr = node [] [child] ∧ Occupancy t false child)
```

### One-shot bundled core (implemented)

The core induction simultaneously produces the key subset, the four kinds of structural information, and the raw height, avoiding five strong inductions that would each re-expand the same set of deletion branches. In the final implementation, [`ComposedPreservation.lean`](../../../CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean) provides all of this at once via `composedDelete_packet`, projected through `composedDelete_nonRoot_preserves` and `composedDelete_rootResult`. The induction motive quantifies over the actually-recursively-deleted key; case 1a/1b recursively delete `maxKey left` / `minKey right` respectively, so the old motive that fixes the outer `x` is unusable.

Public interface for the non-root case:

```lean
theorem composedDelete_nonRoot_preserves
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hinv : NodeWF t false tr)
    (hready : t ≤ numKeys tr) :
    let out := composedDelete t x tr
    KeysSubset out tr ∧
    NodeWF t false out ∧
    heightOf out = heightOf tr
```

Public interface for the root case:

```lean
theorem composedDelete_rootResult
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    let out := composedDelete t x tr
    KeysSubset out tr ∧
    RootDeleteResult t out ∧
    heightOf out = heightOf tr
```

The old component names are retained as projections of these bundled theorems, with mathematically correct hypotheses:

- subset / Sorted / ChildBounded use `NodeWF`;
- occupancy additionally exposes `DeleteReady` and includes `SameDepth`;
- SameDepth + raw height use `ChildBounded + SameDepth`;
- the key-bound wrapper is projected from the subset with hypotheses, no longer an unconditional conclusion.

## Root normalization and public deletion (implemented)

```lean
def normalizeRoot : BTree → BTree
  | node [] [child] => child
  | tr => tr

def composedDeleteRoot (t x : Nat) (tr : BTree) : BTree :=
  normalizeRoot (composedDelete t x tr)
```

The public well-formedness theorems use names consistent with the normalized operation:

```lean
theorem composedDeleteRoot_wellFormed
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    WellFormed t (composedDeleteRoot t x tr)
```

Also provided:

- `composedDeleteRoot_keys_subset`;
- `composedDeleteRoot_height`: the output height equals the input, or is exactly one level lower;
- the contraction bridge `Occupancy t false child → Occupancy t true child`.

`composedDelete` is explicitly the raw node operation; `composedDeleteRoot` is the CLRS algorithm operation that can be called on the root. The old name `composedDelete_wellFormed` was not kept, because it would suggest that the raw operation preserves `WellFormed`, a proposition for which a counterexample already appears above.

## Proof layering of the original design

### 1. Indexing and projections

First prove the following small lemmas to eliminate the unreachable total-function fallbacks on well-formed inputs:

- project the four invariants of a child from `NodeWF`;
- `findChild` lies within the children range of an interior well-formed node;
- when `i > 0`, the separator `ks[i - 1]?` must exist;
- the required sibling lookup exists;
- guard failure together with the occupancy lower bound implies the child has exactly `t - 1` keys;
- parent `SameDepth` implies adjacent siblings have equal height.

### 2. repair packets

Explicitly import `Rotation.lean` and combine the existing lemmas:

- merge: `mergeNodes_{sorted,childBounded,occupancy,sameDepth,height}`;
- rotation: the bundled occupancy/same-depth/height lemmas, plus the 8 Sorted/ChildBounded lemmas in `Rotation.lean`;
- key: `mem_keysOf_mergeNodes`, `mem_keysOf_rotateLeft/Right`;
- positive keys: `allKeysPos_*`, `maxKey_mem`, `minKey_mem`, `maxKey_ge`, `minKey_le`.

This forms three complete packets: merge, borrow-left, and borrow-right.

### 3. parent reassembly

Prove and reuse:

- single-child replacement;
- predecessor / successor separator-key replacement;
- replacement after rotating adjacent children;
- keys/children splice after merge.

Each packet assembles Sorted, ChildBounded, Occupancy, SameDepth, height, and subset in one shot; the main induction is only responsible for orchestrating the semantic branches.

### 4. Main induction

The original design planned to use a generalized `Nat.strongRecOn`:

```lean
∀ x' tr' isRoot,
  heightOf tr' = n →
  NodeWF t isRoot tr' →
  DeleteReady t isRoot tr' →
  ...
```

This scheme originally hoped to avoid using the 35-case `composedDelete.induct` directly, keeping only the leaf, the three separator branches, the four descents with `j > 0`, and the three descents with `j = 0` under the well-formedness hypotheses. The final implementation instead uses the generated `composedDelete.induct`; this is the clearest deviation of the implementation from the design.

## Public interface compatibility (design starting point and result)

The Chapter 18 interface tests at the design starting point required 12 real `splitChild` wrappers; these were an independent issue left over from the earlier migration from identity stubs to the three-argument implementation, not interfaces still missing today. The final implementation has restored these names, with signatures that explicitly include `minDegree`, the child index, and the `Valid` hypothesis; the proofs are derived from the key-multiset permutation of `splitChild_keys_perm`. `Tests/Chapter_18_Interface.lean` now locks down these 12 public names.

## Implementation results and design deviations

| Item | Implementation result |
| --- | --- |
| Main induction | The original proposal was a generalized `Nat.strongRecOn`; the final implementation uses the generated `composedDelete.induct`. |
| bundled core | `composedDelete_packet` in [`ComposedPreservation.lean`](../../../CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation.lean) simultaneously gives key containment, root-sensitive structural results, and raw height preservation. |
| Root normalization | The raw root interface `composedDelete_rootResult` returns `RootDeleteResult`; the public root-deletion API `composedDeleteRoot` contracts the transient empty root via `normalizeRoot`, wrapped by `composedDeleteRoot_{keys_subset,height,wellFormed}`. |
| `splitChild` API | The 12 wrappers were missing at the design starting point; they are now restored, and the interface is locked by `Tests/Chapter_18_Interface.lean`. |
| Exact deletion semantics | Not part of the original structural milestone; subsequently completed with `keyBag` / `Multiset.erase` per the [exact-deletion-semantics plan](../plans/2026-07-30-ch18-exact-deletion-semantics.md), no longer remaining work. |
| Deletion height | `f3f61b4` also completed same-depth/same-height preservation of the raw deletion, and that the public root deletion keeps the height unchanged or decreases it by exactly one. |
| Whole-chapter height | The follow-up milestone on 2026-07-31 completed the minimum key count and the logarithmic height bound; [Chapter 18 current status](../../chapters/chapter-18.md) records the whole-chapter closure at `134/134`. |

## Acceptance record

The design stage required regression coverage:

1. An interior root with one key and two children for `t = 3` satisfies root occupancy, while the corresponding non-root shape is still constrained by the `t` lower bound;
2. A non-root minimal-leaf counterexample shows the old occupancy contract does not hold, and checks that the new theorem must accept ready;
3. An empty-key-descendant counterexample shows the unconditional subset does not hold;
4. After a single-separator root merges, the raw result is a transient empty root, well-formed after `normalizeRoot`;
5. separator predecessor, successor, merge;
6. direct, borrow-left, borrow-right, merge-left, merge-right;
7. The 12 public `splitChild` names are available.

The following Chapter 18 build/interface checks remain available for implementation regression:

```bash
lake build CLRSLean
lake env lean Tests/Chapter_18_Interface.lean
lake env lean Tests/Chapter_18_Root_Occupancy.lean
lake env lean Tests/Chapter_18_Deletion_Interface.lean
lake env lean Tests/Chapter_18_Deletion_Exact_Interface.lean
lake env lean Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
lake env lean Tests/Chapter_18_Height_Interface.lean
git diff --check
```

When the implementation was closed out, `#print axioms` was also run on the headline theorem, confirming that no `sorryAx` exists. The original design gate once included full-site HTML generation via `lake build :literateHtml`; that was the documentation-release check of that time, not a current acceptance requirement after this document was archived.

## Semantic boundary of the original structural milestone (historical)

`KeysSubset` only says that "the result does not add keys out of nowhere"; it is not the same as exact deletion semantics. Therefore the 2026-07-30 structural milestone did not claim to have proven:

- `x` is absent from the result;
- every old key with `y ≠ x` is still present;
- `keysOf` exactly equals multiset/list deletion.

These were explicitly left at the time to independent semantic-correctness theorems, not as hidden hypotheses of the structural-invariant proofs; they were subsequently completed via `keyBag (composedDelete ...) = (keyBag ...).erase x` and the public root-deletion wrapper, and this exact-deletion-semantics gap no longer exists in the current repository.
