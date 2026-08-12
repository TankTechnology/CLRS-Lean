# AFP B-tree Deletion Proof Architecture Investigation (Niels Mündler) — 2026-07-27 Historical Snapshot

> **Timeline.** This document records the investigation as of 2026-07-27. The old
> blocker counts and the "attack order" in the text describe only the state at
> that time; Chapter 18 has since reached **134/134**. This AFP comparison is
> kept to explain the origin of the architecture and the proof-engineering
> context, not to list the current backlog.

Subject of investigation: the AFP entry **A Verified Imperative Implementation of
B-Trees** for Isabelle/HOL. The author listed in the AFP entry's official metadata
is **Niels Mündler**, and the entry date is **2021-02-24**.

- Entry page: https://isa-afp.org/entries/BTree.html
- Functional core theories:
  - https://isa-afp.org/browser_info/current/AFP/BTree/BTree.html
  - https://isa-afp.org/browser_info/current/AFP/BTree/BTree_Set.html
  - https://isa-afp.org/browser_info/current/AFP/BTree/BTree_Height.html

Motivation: in the 2026-07-27 snapshot, well-formedness of Ch18.3 `composedDelete`
was one of the longest-running efforts in the whole project (about 30 days; for
related historical cases see
[`stuck-points-retrospective-2026-07-24.md`](../proof-patterns/stuck-points-retrospective-2026-07-24.md)).
At that time roughly 11 `sorry`s remained, concentrated in `mergeNodes_childBounded`,
key-bound transfer, and non-root leaf Occupancy. This document preserves the
AFP-side proof architecture, the key techniques, and the historical mapping to
CLRS-Lean; the final implementation results are filled in in §5.

---

## 1. Architecture Overview

### 1.1 Datatype and Representation Differences

```isabelle
datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"
```

Keys and subtrees are **stored interleaved**: in `Node ts t`, `ts` is a list of
`(subtree, separator key)` pairs and `t` is the rightmost subtree; `Leaf` is the
empty tree. CLRS-Lean's representation is
`node (keys : List Nat) (children : List BTree)` (parallel lists of
keys/children, where empty children means a leaf). The structures differ; the
table below compares analogous proof obligations and does not treat the
predicates on the two sides as the same logical assertion:

| AFP | CLRS-Lean | Difference |
|---|---|---|
| `bal t` (all subtrees same height + recursive bal) | `SameDepth` + `heightOf` | Both carry equal-leaf-depth and height-related obligations; the encoding interfaces differ |
| `order k t` (non-root `k ≤ len ts ≤ 2k`) / `root_order k` | `Occupancy t isRoot` | Occupancy interval is analogous; the number of pairs corresponds to the number of keys, but the root interface and recursive organization differ |
| `sorted_less (inorder t)` (global inorder sorted) | `Sorted + ChildBounded` | Both share the intra-node sorting and cross-subtree order obligations; AFP's `del_inorder` additionally gives an exact inorder equality |

### 1.2 Deletion Function Decomposition (post-fix style, not CLRS pre-fix style)

```
delete k x t = reduce_root (del k x t)
```

- `del k x`: recursive descent; when a separator key is hit, if the left child is
  `Leaf` it directly removes that pair, otherwise it uses `split_max` (taking the
  largest key of the left subtree to replace the separator key, rather than
  CLRS's predecessor/merge-subtree); after returning, reassembly is done with
  `rebalance_middle_tree` / `rebalance_last_tree`.
- `rebalance_middle_tree k ls sub sep rs t`: a **uniform constructor** that
  absorbs the case where `sub` may be underfull — if both `sub` and its sibling
  have ≥ k pairs it directly puts it back; otherwise it merges wholesale and
  hands the result to `nodeᵢ`.
- `nodeᵢ`: a **normalized constructor shared with insertion**; if `len ≤ 2k` it
  constructs directly, otherwise it splits in half and returns `Upᵢ l a r`. The
  deletion side reuses insertion's split logic and the full set of proven lemmas —
  the most effort-saving design in the whole architecture.
- `split_max k`: walks down the rightmost spine to remove the largest key,
  returning (repaired tree, largest key).
- `reduce_root`: if the root has 0 pairs it collapses to the single subtree —
  **height decreases by one only here**, and `del` itself preserves height
  (`del_height: height (del k x t) = height t`).
- Intermediate-state invariant `almost_order k`: **keeps only the upper bound
  `len ≤ 2k` + subtree `order`, dropping the lower bound**. Underfullness is only
  repaired by merging at the `rebalance_*` sites.

Termination: Isabelle's `fun` terminates automatically, relying on a single
`[termination_simp]` rule:
`split ts y = (ls,(sub,sep)#rs) ⟹ size sub < size (Node ts …)`.
CLRS-Lean instead uses `termination_by heightOf` + `heightOf_mem_lt`. Both sides
share the proof shape of "recursive argument strictly decreases", but the measure
and generation mechanism used are not the same.

### 1.3 Theorem Decomposition

One lemma per function × per invariant, with all inductions using **the function's
own induction principle** `induction k x t rule: del.induct`:

- `nodeᵢ`: `_height` (height unchanged), `_bal`, `_order` (premise `len ≤ 4k+1`),
  `_inorder` (**exact inorder equality**)
- `rebalance_middle_tree`: `_height` / `_bal` / `_order` (+ `_last_order`) / `_inorder`
- `split_max`: `_height` / `_bal` / `_order` / `_inorder`, all needing the helper
  predicate `nonempty_lasttreebal` (at every level on the spine `ts` is nonempty
  and the last subtree has the same height), derived from order+bal by
  `order_bal_nonempty_lasttreebal`
- `del`: `del_height` / `del_bal` / `del_order` (conclusion `almost_order`) / `del_inorder`
- `delete`: `delete_order` / `delete_bal` / `delete_inorder`, closed off via the
  three one-line lemmas `reduce_root_order/bal/inorder`

---

## 2. Four Core Techniques

### Technique A: modeling underfullness with a "weakened invariant", recovering the lower bound at merges

```isabelle
fun almost_order where
  "almost_order k Leaf = True" |
  "almost_order k (Node ts t) =
    (length ts ≤ 2*k ∧ (∀s ∈ set (subtrees ts). order k s) ∧ order k t)"
```

The conclusion of `del_order` is exactly `almost_order` — during the induction
there is **never a need to prove the lower bound at intermediate nodes**. The
lower bound is only restored in `rebalance_middle_tree_order`: the non-merge
branch has premise `length mts ≥ k`, and the merge branch is handed to
`nodeᵢ_order`. This shares the local proof shape of "weaken at intermediate
states, restore at repair points" with the Okasaki pattern of CLRS-Lean's
red-black tree deletion (S8, NoRedRed2 + baldL/baldR); the concrete predicates
and algorithm branches are not isomorphic.

### Technique B: post-merge key-count bound = pure length arithmetic + constructor absorbing overflow

```isabelle
lemma nodeᵢ_order:
  assumes "length ts ≥ k" "length ts ≤ 4*k+1"
    and "∀x ∈ set (subtrees ts). order k x" "order k t"
  shows "order_upᵢ k (nodeᵢ k ts t)"
```

The proof is just cases on `length ts ≤ 2*k`: if so, directly `order`; otherwise,
after `split_half` both sides are `≥ k ∧ ≤ 2k` (arithmetic from the `4k+1` upper
bound). **The contents of the keys play no role at all** — order only counts
length. CLRS-Lean's merge case is simpler: merging two `t-1`-key nodes gives
`2t-1`, which never overflows.

### Technique C: content correctness via inorder equalities rather than subset reasoning

```isabelle
lemma nodeᵢ_inorder: "inorder_upᵢ (nodeᵢ k ts t) = inorder (Node ts t)"
lemma rebalance_middle_tree_inorder:
  assumes "height t = height sub" (…)
  shows "inorder (rebalance_middle_tree k ls sub sep rs t)
       = inorder (Node (ls@(sub,sep)#rs) t)"
```

Rebalancing **preserves inorder verbatim** (the proof is essentially automatic
after `cases sub; cases t`). Consequently `del_inorder` only needs to rewrite
against list-level lemmas such as `del_list_split`, with **no
"result keys ⊆ original keys"-style subset lemmas anywhere**.

### Technique D: the family of bal substitution lemmas

`bal_substitute` / `bal_substitute_subtree` / `bal_substitute_separator` /
`bal_split_last/left/right` — "swapping in a same-height bal subtree / swapping a
separator key preserves bal", each a 2–5-line little lemma, and `del_bal` is
assembled from them. CLRS-Lean already had similar basic lemmas at the time
(`sameDepth_keys_irrel` / `sameDepth_of_uniform`), but as of the 2026-07-27
snapshot it lacked a direct substitution interface for "swapping a child while
preserving SameDepth".

---

## 3. Mapping to CLRS-Lean

### 3.1 The logical boundary of the sorting obligation: global inorder vs. local decomposition

AFP's global `sorted_less (inorder tree)` corresponds to the combined sorting
obligation carried by this project's `Sorted + ChildBounded`. AFP has no
separately named per-subtree `ChildBounded` predicate, but that does not mean AFP
omits the cross-subtree order obligation, nor does it support the conclusion that
"CLRS-Lean's invariant is strictly stronger".

The difference lies in the proof interface: CLRS-Lean maintains the intra-node
`Sorted` and the per-child interval bound `ChildBounded` separately, whereas AFP
expresses ordering on a global inorder sequence and threads the deletion proof
through the exact equality of `del_inorder`. The two implementation options
listed at the time (2026-07-27) were:

- **Option 1 (recommended, small change)**: keep `ChildBounded`, but following the
  idea of Technique C, first prove a membership-characterization lemma:

  ```lean
  k ∈ keysOf (mergeNodes l sep r) ↔ k ∈ keysOf l ∨ k = sep ∨ k ∈ keysOf r
  ```

  Pure List membership unfolding (`keysOf` is `keys ++ flatMap keysOf`; after a
  merge it is `lKeys ++ sep :: rKeys ++ (lCh ++ rCh).flatMap keysOf`, using
  `List.mem_append` and `List.mem_flatMap`; expected < 30 lines). With it, each
  child bound of `mergeNodes_childBounded` is assembled directly by a disjunction
  of the premises and the two sides' `ChildBounded`; the proof decomposition is
  similar to the already-proven `mergeNodes_sorted`.
- **Option 2 (large change, aligning with AFP)**: replace `Sorted` + `ChildBounded`
  with a single global invariant `SortedInorder t := List.Sorted (· ≤ ·) (the
  inorder version of keysOf)`, and prove deletion correctness directly as a
  `del_list`-style equality `keysOf (composedDelete …) = ...`. This eliminates
  all key-bound transfer, but it requires rewriting all of Ch18's existing lemmas,
  so it is not recommended during the closing phase.

### 3.2 The item-by-item mapping table as of 2026-07-27

| CLRS-Lean `sorry`s / stuck points at the time | AFP counterpart | Technique planned to borrow at the time |
|---|---|---|
| `mergeNodes_childBounded` | `nodeᵢ_order` + `bal_list_merge` | key-count part via length arithmetic (Technique B); child interval bounds via the local membership decomposition of §3.1 |
| `keysOf_composedDelete_subset` | AFP provides the relevant content semantics via the stronger `del_inorder` equality | reuse the recursion skeleton + merge membership-characterization lemma |
| `composedDelete_key_bound_lo` / `_hi` | the global sequence semantics of `del_inorder` carries the corresponding order obligation | derive local upper/lower bounds from the key subset |
| proof holes in the four merge branches | `del`'s hit branch (AFP uses `split_max` + rebalance) | use the `mergeNodes_*` preservation lemmas + IH |
| non-root leaf `Occupancy t false` | `del_order`'s Leaf base case + `almost_order` | see §3.4; judged at the time that a pre-fix guard was needed |

### 3.3 The key-subset and local-bound proofs planned at the time

- `keysOf_composedDelete_subset`: the plan at the time was for the strong
  induction to reuse the skeleton of `composedDelete_childBounded`, with three
  new pieces: (1) the merge branch uses the membership-characterization lemma of
  §3.1 + IH; (2) the direct-recursion branch uses `List.mem_or_eq_of_mem_set`;
  (3) the leaf branch uses `mem_of_sortedRemove`.
- `composedDelete_key_bound_lo` (and the symmetric hi version): planned at the
  time as a short corollary of the subset
  (`intro k' hk'; exact hlo k' (keysOf_composedDelete_subset … hk')`). The goal
  was to have the various local upper/lower-bound proofs all derive uniformly
  from the content-containment relation.

### 3.4 The non-root leaf Occupancy obstacle as judged at the time

As of 2026-07-27, after deletion a leaf could be left with only `t-2` keys, and
the `composedDelete` version at the time had no corresponding repair logic; the
goal under that version therefore could not be derived from the existing
premises. Two paths were extracted at the time from comparing with the AFP
architecture:

- **Path A (AFP route, post-fix style)**: introduce `AlmostOccupancy` (dropping
  the lower bound, keeping only the `≤ 2t-1` upper bound + recursion), prove by
  induction that `composedDelete` preserves `AlmostOccupancy`, and then write a
  separate `rebalance` to restore the lower bound — i.e., change the algorithm to
  post-fix style; a large change.
- **Path B (CLRS pre-fix route, recommended)**: add a guard before recursing into
  a child: if the target child has only `t-1` keys, first `rotateRight` (there was
  already `rotateRight_preserves` at the time) or add `rotateLeft` + merge to
  bring it to ≥ t keys, then recurse. This way the IH is used directly on a child
  satisfying the lower bound, and the `t-2` leaf base case is excluded by the
  guard. The file-header comment at the time already planned this direction; the
  gap was `rotateLeft` and its preservation lemmas.

The final implementation took the CLRS pre-fix route; §5 records the completed
rotation repair and reassembly results.

### 3.5 Engineering suggestion: switch to the function's own induction principle

All of AFP's del theorems use `induction k x t rule: del.induct` — the function's
own induction principle, with cases automatically aligned to the function
branches. In the 2026-07-27 CLRS-Lean snapshot, the four `composedDelete_*`
component lemmas had been manually built four times with `Nat.strongRecOn` +
motive, with the same branch-unfolding boilerplate copied four times, and each
copy still left merge proof holes. Lean 4 automatically generates
`composedDelete.induct` for functions defined with `termination_by`, and
`induction tr using composedDelete.induct` yields IHs organized by branch
(including an IH for the merged node in the merge branch). This suggestion was
later realized as bundled induction around `NodeWF`; see §5.

### 3.6 The attack order suggested at the time (2026-07-27)

The plan at the time was to proceed in the following dependency order:

1. `mem_keysOf_mergeNodes` (membership characterization, pure List) →
2. `mergeNodes_childBounded` (following the decomposition of `mergeNodes_sorted`) →
3. `keysOf_composedDelete_subset` (existing skeleton + membership characterization) →
4. `composedDelete_key_bound_lo` / `_hi` (subset corollaries) →
5. the four merge branches (using the aforementioned merge preservation lemmas + IH) →
6. `rotateLeft` + the pre-fix guard → non-root leaf Occupancy.

At the time it was estimated that the first four steps needed no algorithm
changes, step five depended on the first two, and step six required modifying
`composedDelete`. This order is now merely a historical execution record, not a
list of outstanding items.

---

## 4. Remarks and honest disclosure

- The AFP technique descriptions in this document are based on a remote reading
  of the theory sources on 2026-07-27; on the CLRS-Lean side, things are now
  located by module and theorem names, with fragile source line numbers no longer
  kept.
- AFP's deletion is **post-fix + split_max**, while CLRS-Lean deliberately takes
  the CLRS textbook's pre-fix (borrow/merge before descent) route to stay
  textbook-faithful, so its algorithm structure cannot be adopted wholesale; what
  is transferable is the **proof organization** (Techniques A–D, the induction
  principle, the inorder-equality idea), not the function definitions.
- The effort estimates and "gap" judgments in the text all belong to the
  2026-07-27 snapshot; whether they were subsequently realized should be judged
  against the implementation results in §5 and the current Chapter 18 section
  notes.

---

## 5. Subsequent implementation results (as of 2026-07-31)

| Problem area as of 2026-07-27 | Subsequent outcome |
|---|---|
| merge content and bounds | `mem_keysOf_mergeNodes` gives an exact membership decomposition; `mergeNodes_childBounded`, `mergeNodes_nodeWF`, `spliceMerged_packet`, and other merge child-bounded / parent reassembly lemmas complete the local preservation and parent-node reassembly. |
| rotation sorting repair | the `Sorted`, `ChildBounded`, `NodeWF`, and repaired-`DeleteReady` results for `rotateLeft` / `rotateRight` are all established, with `rotateLeft_reassembly_packet` / `rotateRight_reassembly_packet` completing the reassembly of the recursive results. |
| bundled recursive invariant | `NodeWF` bundles `Sorted`, `ChildBounded`, `Occupancy`, `SameDepth`; `composedDelete_packet` delivers key subset, structural results, and original-height preservation in a single recursive proof. |
| induction aligned with function branches | the core recursive proof uses Lean's function-generated `composedDelete.induct`, with IHs aligned to the predecessor, successor, merge, rotation, and direct-descent branches. |
| exact deletion | `composedDelete_keyBag` proves `keyBag (composedDelete t x tr) = (keyBag tr).erase x`, i.e., exactly one occurrence of the requested key is deleted, rather than merely proving that the result keys are a subset of the input keys. |
| height | `composedDelete_sameDepth_height` gives same-depth and raw-height preservation; `composedDeleteRoot_height` proves that after root normalization the height is unchanged or decreases by exactly one. |

Together with search, insertion, and the minimum-key-count/log-height bounds,
these results subsequently pushed Chapter 18 to **134/134**. In the current
functional B-tree model, there are **no remaining Chapter 18 core proof items**.
