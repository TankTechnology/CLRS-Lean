# Reproducible Source-Review Evidence

These examples target the source snapshot recorded by this directory's index.
Save each code block as a separate temporary `.lean` file and run
`lake env lean <temporary-file>` from the repository root to reproduce it. The
examples do not modify the original algorithms, add project axioms, or use
`sorry` or `native_decide`.

## Chapter 13: rotation loses a reachable key and sentinel representation is not unique

Lean exits with status 0; the kernel checks every example.

```lean
import CLRSLean.FourthEdition.Chapter_13

open CLRS.Chapter13
open CLRS.Chapter13.RBStore

namespace Chapter13Audit

def n1 : RBNode := ⟨1, .black, 0, 2, 0⟩
def n2 : RBNode := ⟨2, .red, 0, 0, 1⟩
def initial : RBStore :=
  ⟨fun i => if i = 1 then some n1 else if i = 2 then some n2 else none, 1⟩

def beforeTree : RBTree := .node .black .empty 1 (.node .red .empty 2 .empty)
def afterRootTree : RBTree := .node .black .empty 1 .empty

example : Represents initial beforeTree := by
  apply StoreRepr.node 1 n1 .empty (.node .red .empty 2 .empty) 1 .black
  · rfl
  · exact StoreRepr.nil
  · apply StoreRepr.node 2 n2 .empty .empty 2 .red
    · rfl
    · exact StoreRepr.nil
    · exact StoreRepr.nil
    · rfl
    · rfl
  · rfl
  · rfl

-- A left rotation at the root keeps root = 1 instead of promoting node 2.
example : (rotateLeftP initial 1).1.root = 1 := rfl
example : Represents (rotateLeftP initial 1).1 afterRootTree := by
  apply StoreRepr.node 1 ⟨1, .black, 0, 0, 2⟩ .empty .empty 1 .black
  · rfl
  · exact StoreRepr.nil
  · exact StoreRepr.nil
  · rfl
  · rfl
example : RBTree.keys beforeTree = [1, 2] := rfl
example : RBTree.keys afterRootTree = [1] := rfl

-- The representation accepts a nonempty tree at the sentinel address.
def sentinelNode : RBNode := ⟨7, .black, 0, 0, 0⟩
def cyclic : RBStore := ⟨fun i => if i = 0 then some sentinelNode else none, 0⟩
example : Represents cyclic .empty := StoreRepr.nil
example : Represents cyclic (.node .black .empty 7 .empty) := by
  apply StoreRepr.node 0 sentinelNode .empty .empty 7 .black
  · rfl
  · exact StoreRepr.nil
  · exact StoreRepr.nil
  · rfl
  · rfl

end Chapter13Audit
```

## Chapter 27: unsatisfiable algorithm interface

The reviewer and primary auditor ran this independently with status 0. It proves
that every `Algorithm (Fin (k + 1)) k` implies `False`.

```lean
import CLRSLean.FourthEdition.Chapter_27

example (k : Nat) (A : CLRS.OnlineCaching.Algorithm (Fin (k + 1)) k) : False := by
  have h := A.step_size Finset.univ (0 : Fin (k + 1))
  rw [A.step_hit Finset.univ (0 : Fin (k + 1)) (Finset.mem_univ _)] at h
  simp at h
```

## Chapter 14: LCS call count and an independent tabular expression

Lean exits with status 0; `counted_value` is a kernel-checked value-preservation
theorem. The four `#eval` commands produce 503, 36, 25739, and 81. These numbers
are execution results rather than a new asymptotic-bound proof.

```lean
import CLRSLean.FourthEdition.Chapter_14.Section_14_4_Longest_Common_Subsequence

namespace LCSAudit

def counted : List Nat → List Nat → Nat × Nat
  | [], _ => (0, 1)
  | _, [] => (0, 1)
  | a :: xs, b :: ys =>
      if a = b then
        let r := counted xs ys
        (r.1 + 1, r.2 + 1)
      else
        let l := counted xs (b :: ys)
        let r := counted (a :: xs) ys
        (max l.1 r.1, l.2 + r.2 + 1)

-- Instrument exactly the branches of the public recursive implementation.
theorem counted_value (xs ys : List Nat) :
    (counted xs ys).1 = CLRS.Chapter15.lcsLength xs ys := by
  fun_induction CLRS.Chapter15.lcsLength xs ys <;>
    simp_all [counted]

-- Equal-length disjoint inputs: the invocation count greatly exceeds the
-- independent quadratic table-cell expression (not itself an operation count).
#eval (counted (List.replicate 5 0) (List.replicate 5 1)).2
#eval CLRS.Chapter15.lcsTableCells 5 5
#eval (counted (List.replicate 8 0) (List.replicate 8 1)).2
#eval CLRS.Chapter15.lcsTableCells 8 8

end LCSAudit
```


## Chapter 17: interval insertion loses equal-low endpoints

The reviewer and primary auditor ran this independently with status 0. The
initial tree satisfies the existing augmentation invariant and BST condition;
inserting a distinct interval leaves the tree unchanged and omits a query match
that should exist.

```lean
import CLRSLean.FourthEdition.Chapter_17
open CLRS.Chapter14
private def initial : AugmentedRBTree Interval Nat :=
  .node .black .empty (0,1) 1 .empty
private def afterInsert :=
  AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt (0,10) initial
example : AugmentedRBTree.WellAugmented IntervalTree.maxHighAug initial := by
  simp [initial, AugmentedRBTree.WellAugmented, AugmentedRBTree.realAug, IntervalTree.maxHighAug, Interval.high]
example : IntervalTree.IsBST (AugmentedRBTree.toIntervalTree initial) := by
  simp [initial, AugmentedRBTree.toIntervalTree, IntervalTree.IsBST, IntervalTree.allLowLE, IntervalTree.allLowGE, IntervalTree.keys, AugmentedTree.keys]
example : afterInsert = initial := by rfl
example : IntervalTree.intervalSearch? (AugmentedRBTree.toIntervalTree afterInsert) (5,5) = none := by decide
example : Interval.overlaps (0,10) (5,5) = true := by decide
```
