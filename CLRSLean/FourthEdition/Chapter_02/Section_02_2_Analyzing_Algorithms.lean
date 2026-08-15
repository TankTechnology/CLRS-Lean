import Mathlib

/-!
# CLRS Section 2.2 - Analyzing algorithms

This file records the first lightweight cost model used in the Chapter 2
workflow.  It does not try to formalize a full RAM model yet.  Instead it
captures the standard insertion-sort worst-case comparison count as a triangular
sum and proves a quadratic upper bound.
-/

namespace CLRS
namespace Chapter02

/-- The triangular sum {lit}`1 + 2 + ... + n`. -/
def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

/-- A small eventual upper-bound predicate for chapter-level runtime claims. -/
def EventuallyBoundedBy (f g : Nat → Nat) : Prop :=
  ∃ c n₀, 0 < c ∧ ∀ n, n₀ ≤ n → f n ≤ c * g n

/-- The usual worst-case comparison count for insertion sort on {lit}`n` elements. -/
def insertionSortWorstComparisons (n : Nat) : Nat :=
  triangular (n - 1)

theorem triangular_le_square (n : Nat) : triangular n ≤ n * n := by
  induction n with
  | zero =>
      simp [triangular]
  | succ n ih =>
      simp [triangular]
      nlinarith

theorem insertionSortWorstComparisons_quadratic (n : Nat) :
    insertionSortWorstComparisons n ≤ n * n := by
  unfold insertionSortWorstComparisons
  exact (triangular_le_square (n - 1)).trans (by nlinarith [Nat.sub_le n 1])

theorem insertionSortWorstComparisons_eventually_quadratic :
    EventuallyBoundedBy insertionSortWorstComparisons (fun n => n * n) := by
  refine ⟨1, 0, by decide, ?_⟩
  intro n _hn
  simpa using insertionSortWorstComparisons_quadratic n

end Chapter02
end CLRS
