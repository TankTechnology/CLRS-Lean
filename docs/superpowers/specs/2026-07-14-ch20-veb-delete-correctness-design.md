# Ch20.3 Recursive vEB Deletion Correctness Design

## Goal

Close the five unfinished branches in `VEBTreeMM.delete_toFinset` without
weakening the CLRS recursive deletion algorithm.  The finished public theorem
must require a representation invariant, prove that deletion preserves that
invariant, and prove exact refinement to `Finset.erase`.

## Scope

This pass covers:

- a semantic well-formedness predicate for `VEBTreeMM`;
- well-formedness of `empty`;
- a bundled deletion theorem proving invariant preservation and represented-set
  correctness;
- projection theorems `delete_wellFormed` and `delete_toFinset`;
- Chapter 20 interface checks and honest status documentation;
- removal of all executable `sorry` markers from Section 20.3.

This pass does not claim correctness for `VEBTreeMM.successor` or
`VEBTreeMM.predecessor`, and it does not replace the current placeholder cost
functions with a control-flow-faithful runtime semantics.  Those remain named
partial targets.

## Representation invariant

Two small predicates state that an optional cached extremum exactly describes a
finite set:

```lean
def MinCorrect (mn : Option Nat) (s : Finset Nat) : Prop :=
  match mn with
  | none => s = ∅
  | some m => m ∈ s ∧ ∀ y ∈ s, m ≤ y

def MaxCorrect (mx : Option Nat) (s : Finset Nat) : Prop :=
  match mx with
  | none => s = ∅
  | some m => m ∈ s ∧ ∀ y ∈ s, y ≤ m
```

`WellFormed` is structural.  A leaf requires both cached extrema to be correct
for the set represented by its two bits.  A node requires:

1. its cached minimum and maximum are correct for the whole `toFinset`;
2. its stored minimum is detached from every cluster payload, matching the CLRS
   representation that keeps the minimum outside the clusters;
3. `hi` occurs in `summary.toFinset` exactly when `clusters hi` is nonempty;
4. the summary and every cluster are recursively well-formed.

The detached-minimum clause is necessary.  Extrema correctness alone permits a
second copy of the minimum inside a cluster; promoting that copy during
delete-minimum would leave the erased key represented.

## Proof interface

The proof truth source is a bundled theorem:

```lean
theorem delete_correct {k : Nat} (v : VEBTreeMM k) (x : Nat)
    (hwf : WellFormed v) :
    WellFormed (delete x v) ∧
      (delete x v).toFinset = v.toFinset.erase x
```

It is proved by strong induction on the universe level.  Recursive calls use
both projections of the induction hypothesis: represented-set equality rewrites
cluster and summary contents, while preserved well-formedness turns cached
`minimum`/`maximum` tests into facts about emptiness and extrema.

The public convenience theorems are:

```lean
theorem delete_wellFormed ... : WellFormed (delete x v)
theorem delete_toFinset ... :
  (delete x v).toFinset = v.toFinset.erase x
```

Local lemmas expose the proof surface needed by the algorithm:

- `minimum_none_iff_toFinset_empty` and its nonempty counterpart;
- `minimum_mem`, `minimum_le`, `maximum_mem`, and `le_maximum`;
- summary membership iff cluster nonemptiness;
- membership lemmas for a single `Function.update`d cluster family;
- high/low/index equality and inequality bridges already present in the file.

## Algorithm changes

The existing recursive `delete` definition is retained.  If a red test exposes
a real implementation error, only the affected branch is changed.  No
Finset-rebuild implementation is allowed because that would bypass the CLRS
algorithm being formalized.

## Verification

The interface test first names `WellFormed`, `empty_wellFormed`,
`delete_correct`, `delete_wellFormed`, and `delete_toFinset`; it must fail before
the implementation exists.  Development then uses narrow Section 20.3 builds.

Completion requires fresh successful runs of:

```text
lake build CLRSLean.Chapter_20.Section_20_3_Recursive_VEB
lake env lean Tests/Chapter_20_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_20 Tests/Chapter_20_Interface.lean
python3 scripts/check_repository.py
lake build CLRSLean
lake build :literateHtml
git diff --check
```

`#print axioms CLRS.Chapter20.VEBTreeMM.delete_correct` must contain no
`sorryAx` or project axiom.
