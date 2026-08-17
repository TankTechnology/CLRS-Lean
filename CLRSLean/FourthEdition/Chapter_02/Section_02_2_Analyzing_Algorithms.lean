import Mathlib

/-!
# CLRS Section 2.2 - Analyzing algorithms

This file records the first lightweight cost model used in the Chapter 2
workflow.  It does not try to formalize a full RAM model yet.  Instead it
captures the standard insertion-sort worst-case comparison count as a triangular
sum and proves a quadratic upper bound.

## Known simplifications

* `EventuallyBoundedBy` is an O-notation upper-bound predicate; the textbook
  uses Θ-notation (both upper and lower bounds) in §2.2.  The lower-bound
  direction is a later strengthening target.
* The cost model tracks only the while-loop comparison count via `triangular`;
  it does not account for for-loop overhead, assignment statements, or the
  full line-by-line cost table in CLRS p. 25.
* Discursive content (why worst-case analysis is preferred, RAM-model
  instruction set enumeration) is not formalized — this is a reasonable
  omission for a theorem-oriented companion.
* `Nat` subtraction truncates to 0 when `n = 0`, so `triangular (n - 1)` gives
  `triangular 0 = 0` for `n = 0`, which is consistent with the textbook
  convention of zero comparisons for an empty input.
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
