import Mathlib

/-!
# CLRS Section 2.2 - Insertion-sort line-cost definitions

This module represents the seven charged lines in the textbook insertion-sort
cost table.  The outer-loop index `k` ranges over `0, ..., n - 2` and
corresponds to the textbook index `i = k + 2`.
-/

namespace CLRS
namespace Chapter02

/-- The triangular sum {lit}`1 + 2 + ... + n`. -/
def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

/-- The symbolic costs attached to executable lines 1, 2, and 4--8. -/
@[ext] structure InsertionSortLineCosts where
  c₁ : Nat
  c₂ : Nat
  c₄ : Nat
  c₅ : Nat
  c₆ : Nat
  c₇ : Nat
  c₈ : Nat
deriving DecidableEq, Repr

/-- The execution-count column of the CLRS insertion-sort cost table. -/
@[ext] structure InsertionSortLineCounts where
  forLoopTests : Nat
  keyAssignments : Nat
  indexInitializations : Nat
  whileLoopTests : Nat
  shifts : Nat
  decrements : Nat
  finalAssignments : Nat
deriving DecidableEq, Repr

/-- Sum of the textbook `tᵢ` values for `i = 2, ..., n`. -/
def insertionSortWhileTestSum (n : Nat) (t : Nat → Nat) : Nat :=
  ∑ k ∈ Finset.range (n - 1), t (k + 2)

/-- Sum of the loop-body counts `tᵢ - 1` for `i = 2, ..., n`. -/
def insertionSortBodyIterationSum (n : Nat) (t : Nat → Nat) : Nat :=
  ∑ k ∈ Finset.range (n - 1), (t (k + 2) - 1)

/-- Derive all seven line counts from input size and while-test trace. -/
def insertionSortLineCounts (n : Nat) (t : Nat → Nat) : InsertionSortLineCounts where
  forLoopTests := n
  keyAssignments := n - 1
  indexInitializations := n - 1
  whileLoopTests := insertionSortWhileTestSum n t
  shifts := insertionSortBodyIterationSum n t
  decrements := insertionSortBodyIterationSum n t
  finalAssignments := n - 1

/-- Evaluate one symbolic cost row against one execution-count row. -/
def InsertionSortLineCosts.evaluate
    (costs : InsertionSortLineCosts) (counts : InsertionSortLineCounts) : Nat :=
  costs.c₁ * counts.forLoopTests +
    costs.c₂ * counts.keyAssignments +
    costs.c₄ * counts.indexInitializations +
    costs.c₅ * counts.whileLoopTests +
    costs.c₆ * counts.shifts +
    costs.c₇ * counts.decrements +
    costs.c₈ * counts.finalAssignments

/-- Complete line-by-line running time for input size `n` and trace `t`. -/
def insertionSortRunningTime
    (costs : InsertionSortLineCosts) (n : Nat) (t : Nat → Nat) : Nat :=
  costs.evaluate (insertionSortLineCounts n t)

end Chapter02
end CLRS
