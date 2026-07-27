# Chapter 20 Recursive van Emde Boas Completion Design

## Goal

Complete the advertised mathematical and algorithmic content of CLRS Chapter
20 on the existing recursive `VEBTreeMM` model.  Every recursive vEB operation
must preserve the representation invariant, refine the Section 20.2 finite-set
specification, and carry a control-flow-aware `O(log log u)` cost theorem over
the tower universe `uSize k = 2 ^ (2 ^ k)`.

This design is the completion contract for GitHub issues #12, #42, and #50.
It supersedes their currently inconsistent open/closed state: #12 and #42 are
closed even though several of their acceptance items remain absent on `main`,
while #50 is open although its deletion refinement theorem is already proved.

## Completion boundary

The completed chapter includes:

1. the existing `u = 2` Boolean leaf as the word-level base case;
2. exact high/low/index decomposition and universe bounds;
3. a recursive summary/cluster representation with cached minimum and maximum;
4. semantic correctness of `member`, `minimum`, `maximum`, `insert`,
   `successor`, `predecessor`, and `delete`;
5. preservation of the cached-extrema, detached-minimum, summary, and recursive
   cluster invariants by both updates;
6. cost definitions that select the same recursive branch as each operation;
7. linear-in-`k` depth/work bounds and CLRS-facing `O(log log u)` packaging;
8. public interface checks, axiom audits, proof ledgers, chapter prose, and
   GitHub issue evidence synchronized with the kernel-checked implementation.

Concrete heap allocation, pointer ownership, cache behavior, and hardware
cycle counts are outside this completion boundary.  They are a separate
imperative refinement layer, not part of the three Chapter 20 issue acceptance
contracts.  The cost model treats cached-field access, arithmetic, and a fixed
number of branch tests at one universe level as constant work.

## Current state and missing obligations

Sections 20.1 and 20.2 already provide the arithmetic and finite-set truth
source.  Section 20.3 already provides:

- `VEBTree` membership and insertion refinement;
- `VEBTreeMM`, `minimum`, `maximum`, `member`, `insert`, `successor`,
  `predecessor`, and `delete` implementations;
- `VEBTreeMM.WellFormed`, including detached minimum and exact
  summary/nonempty-cluster correspondence;
- `VEBTreeMM.delete_correct`, proving invariant preservation and exact
  `Finset.erase` refinement;
- the tower logarithm lemmas and a generic `O(log log u)` wrapper.

The remaining obligations are real, not documentation-only:

- `VEBTreeMM.insert` has no invariant/refinement theorem.  Its node branch also
  lacks an idempotent `x = minimum` guard.  Inserting the stored minimum can
  place a second copy into a cluster and violate `node_min_detached`.
- recursive `VEBTreeMM.successor` and `predecessor` have no least-greater /
  greatest-less correctness theorems;
- the existing successor, predecessor, and delete costs always descend through
  a fixed dummy cluster and therefore do not witness the algorithms' actual
  branch choices;
- Chapter 20 guides and GitHub issue states do not agree with the source.

## Representation and update architecture

`VEBTreeMM.WellFormed` remains the single representation invariant.  The
existing `delete_correct` theorem is retained as the deletion truth source.
Insertion receives the symmetric bundled theorem:

```lean
theorem insert_correct {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) (hx : x < uSize k) :
    WellFormed (insert x v) ∧
      (insert x v).toFinset = Finset.insert x v.toFinset
```

The implementation first returns the node unchanged when `x` equals its
detached cached minimum.  Otherwise it keeps the existing CLRS lazy-min
algorithm:

- when `x < minimum`, store `x` as the new detached minimum and recursively
  insert the old minimum;
- when the destination cluster is empty, recursively update only the summary
  and create the cluster with `singleton` in constant work;
- when the cluster is nonempty, recursively update only that cluster.

Before the bundled proof, the library establishes:

```lean
theorem singleton_toFinset ... : (singleton k x hx).toFinset = {x}
theorem singleton_wellFormed ... : WellFormed (singleton k x hx)
```

Local insertion lemmas normalize `Function.update`, summary membership, cached
extrema, and the detached-minimum obligation.  Public projections are
`insert_wellFormed` and `insert_toFinset`.

## Successor and predecessor specifications

The Section 20.2 result shapes remain the public contract.  For a well-formed
recursive tree:

```lean
theorem successor_correct {k : Nat} {v : VEBTreeMM k} {x y : Nat}
    (hwf : WellFormed v) (hsucc : successor x v = some y) :
    y ∈ v.toFinset ∧ x < y ∧
      ∀ z, z ∈ v.toFinset → x < z → y ≤ z

theorem predecessor_correct {k : Nat} {v : VEBTreeMM k} {x y : Nat}
    (hwf : WellFormed v) (hpred : predecessor x v = some y) :
    y ∈ v.toFinset ∧ y < x ∧
      ∀ z, z ∈ v.toFinset → z < x → z ≤ y
```

Strong induction on `k` follows the executable branches:

- the cached minimum/maximum shortcut;
- a recursive result inside the query cluster;
- a summary result selecting the next/previous nonempty cluster;
- reconstruction with that cluster's cached minimum/maximum;
- the out-of-universe and no-candidate cases.

The proof reuses `node_summary_mem_iff`, `node_cluster`, `node_summary`,
`index_lt_index_of_high_lt`, and `index_le_index_of_low_le`.  Small new helper
lemmas cover strict order for two offsets in one cluster and high/low recovery
from a represented cluster key.

The public surface mirrors Section 20.2:

- `successor_mem`, `successor_gt`, `successor_le`,
  `successor_lt_uSize`, `successor_none_iff`,
  `successor_none_of_no_gt`, and `successor_ne_none_of_exists_gt`;
- `predecessor_mem`, `predecessor_lt`, `le_predecessor`,
  `predecessor_lt_uSize`, `predecessor_none_iff`,
  `predecessor_none_of_no_lt`, and `predecessor_ne_none_of_exists_lt`.

The strong `*_correct` and `*_none_iff` theorems are the truth sources; the
remaining declarations are projections rather than independent proofs.

## Control-flow-aware cost semantics

Each operation receives either an instrumented evaluator whose first projection
is the existing result and whose second projection is the recursive cost, or a
constant-cost witness for the cached extrema:

```lean
memberWithCost      : Nat → VEBTreeMM k → Bool × Nat
minimumWithCost     : VEBTreeMM k → Option Nat × Nat
maximumWithCost     : VEBTreeMM k → Option Nat × Nat
insertWithCost      : Nat → VEBTreeMM k → VEBTreeMM k × Nat
successorWithCost   : Nat → VEBTreeMM k → Option Nat × Nat
predecessorWithCost : Nat → VEBTreeMM k → Option Nat × Nat
deleteWithCost      : Nat → VEBTreeMM k → VEBTreeMM k × Nat
```

The corresponding result theorems prevent the instrumentation from drifting:

```lean
(insertWithCost x v).1 = insert x v
(successorWithCost x v).1 = successor x v
(predecessorWithCost x v).1 = predecessor x v
(deleteWithCost x v).1 = delete x v
```

`minimumWithCost` and `maximumWithCost` read their cached fields and have cost
one.  `memberWithCost`, `insertWithCost`, `successorWithCost`, and
`predecessorWithCost` charge one unit for the current universe level and follow
exactly one recursive branch.  Their costs are bounded by `k + 1`.

Deletion requires an explicit CLRS accounting lemma.  If deletion from a
nonempty cluster makes that cluster empty, exact `Finset.erase` refinement
implies that the old cluster was a singleton containing the deleted offset.
Its recursive deletion therefore performs only constant local work; the
summary call is the unique nonconstant recursive descent.  The cost evaluator
charges this immediate singleton deletion inside the current level's constant
work and follows the summary branch.  A separate recursion-depth theorem makes
the `≤ k + 1` claim precise.  If an exact unit count of every syntactic function
entry is exposed, it may use a constant-factor linear bound; the public
asymptotic result must not pretend that two constant local tests are one machine
instruction.

For every nonconstant operation, the final theorem composes the linear
tower-level bound with `VEBTree.loglog_uSize` and the Chapter 3 `isBigO`
wrapper.  Cached minimum and maximum receive direct constant-cost theorems.
The headline chapter theorem states that all seven recursive operations have
constant or `O(log log u)` cost as appropriate.

## File and interface strategy

The existing Section 20.3 file is already the canonical module and the site
expects exactly three Chapter 20 section modules.  To avoid a disruptive module
move during a proof-critical pass, new definitions and proofs remain in:

- `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`

The public contract is extended first in:

- `Tests/Chapter_20_Interface.lean`

Completion metadata is synchronized in:

- `CLRSLean/Chapter_20.lean`;
- `CLRSLean/Status.lean`;
- `docs/clrs-proof-progress.csv`;
- `docs/proof-map.md`;
- `docs/chapters/chapter-20.md`.

No `literate.toml` structural change is needed because no module is added or
moved.  Its Chapter 20 ordering and titles are nevertheless part of the final
site consistency check.

## Test-first implementation order

1. Add missing insertion theorem names to `Tests/Chapter_20_Interface.lean` and
   observe the expected unknown-identifier failures.
2. Fix duplicate-minimum insertion and prove singleton plus bundled insertion
   correctness; run the narrow Section 20.3 and interface checks.
3. Add successor strong-spec and wrapper names to the interface, observe the
   failures, then prove the successor family.
4. Repeat the red-green cycle for predecessor.
5. Add all seven cost/result interfaces, including cached-extrema constant
   costs, member depth, four instrumented complex operations, linear bounds,
   and asymptotic theorem names to the interface before implementing them.
6. Synchronize reader-facing status only after all headline theorems compile.

No finite-set rebuild may replace the recursive algorithms.  Finsets remain
specifications and proof tools, not executable shortcuts.

## Verification and completion evidence

Completion requires fresh successful evidence for every gate below:

```text
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
python3 scripts/check_repository.py
lake build CLRSLean
lake build :literateHtml
git diff --check
```

`#print axioms` is run for `insert_correct`, `successor_correct`,
`predecessor_correct`, `delete_correct`, and the headline asymptotic theorem.
No result may depend on `sorryAx`, `propext` beyond Mathlib's normal theorem
surface, or a project-defined axiom.

The progress ledger may move Chapter 20 from `partial` to
`main-proof-complete-for-correctness` only after the full matrix above passes.
The remaining concrete-memory refinement must be named explicitly and must not
be described as an unfinished mathematical vEB operation.

## GitHub issue and remote-state policy

Issue updates are evidence-driven:

- #42 receives the insertion and neighbor-query theorem names, cost theorems,
  verification output, and the completing commit;
- #50 receives deletion correctness plus the faithful cost/depth theorem and is
  closed only when both parts satisfy its acceptance contract;
- #12 receives the all-operation completion matrix and is treated as the epic
  completion record.

If an issue must be reopened while implementation is incomplete, its comment
must identify the missing acceptance items without blaming the earlier work.
At completion, comments distinguish the abstract unit-cost model from concrete
hardware timing.

All proof work stays on `codex/ch20-complete` until the full gate passes.  The
final integration is a non-force fast-forward of `main`.  Unrelated branches
and pull requests are not modified.  If the feature branch is ever pushed, it
is removed from the remote after successful integration so the remote retains
only active work.
