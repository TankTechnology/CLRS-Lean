import Mathlib
import CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.FourthEdition.Chapter_02.Section_02_2_Analyzing_Algorithms.LineCost

/-!
# CLRS Section 2.2 - Analyzing algorithms

This file records the Chapter 2 cost models.  The line-cost development assigns
the textbook constants `c₁`, `c₂`, and `c₄`--`c₈`, derives the execution count
of every charged pseudocode line from supplied symbolic counts `tᵢ`, and proves
the full seven-term equation for `T(n)`. Its best- and worst-case
specializations are exact substitutions into that table; these parameters are
not extracted from an input execution.

The recursive comparison counter is bounded on every input by
`insertionSortComparisons_le_worst`. The explicit descending family
`insertionSortWorstInput` attains that bound at every size, including zero.
`insertionSortWorstComparisons_isGreatest` identifies the size formula with the
maximum of actual length-n comparison counts, and
`insertionSortComparisons_worst_case_theta` combines this connection with Θ(n²).
Already-sorted input has exactly n-1 comparisons and the existing Θ(n) bound.

A `ThetaBoundedBy` predicate packages the O and Ω directions into a single
Θ-notation claim, matching the textbook's asymptotic language in §2.2.

## Known simplifications

* `EventuallyBoundedBy` is an O-notation upper-bound predicate; the textbook
  uses Θ-notation (both upper and lower bounds) in §2.2.  The
  `ThetaBoundedBy` wrapper combines both directions to recover the Θ claim.
  `insertionSortComparisons_worst_case_theta` connects the worst-case Θ(n²)
  formula to the attained maximum of actual runs; the best-case Θ(n) bound is
  `insertionSortBestComparisons_theta_linear`.
* The line-cost table is a symbolic unit-cost model.  It accounts for the
  for-loop test, assignments, while-loop tests, shifts, and decrements, but it
  is not an operational word-RAM or mutable-array semantics. No validity
  predicate asserts that every supplied `tᵢ` sequence is a realizable trace.
* Discursive content (why worst-case analysis is preferred, RAM-model
  instruction set enumeration) is not formalized — this is a reasonable
  omission for a theorem-oriented companion.
* `Nat` subtraction truncates to 0 when `n = 0`, so `triangular (n - 1)` gives
  `triangular 0 = 0` for `n = 0`, which is consistent with the textbook
  convention of zero comparisons for an empty input.

## Implementation details

* [Line-cost facade](CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms/LineCost/)
  ([definitions](CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms/LineCost/Definitions/),
  [formula](CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms/LineCost/Formula/),
  [best/worst cases](CLRSLean/FourthEdition/Chapter_02/Section_02_2_Analyzing_Algorithms/LineCost/BestWorst/))
-/

namespace CLRS
namespace Chapter02

/-- A small eventual upper-bound predicate for chapter-level runtime claims. -/
def EventuallyBoundedBy (f g : Nat → Nat) : Prop :=
  ∃ c n₀, 0 < c ∧ ∀ n, n₀ ≤ n → f n ≤ c * g n

/--
A Θ-notation predicate: `f ∈ Θ(g)` when both `f ∈ O(g)` and `g ∈ O(f)`,
i.e. `f` is asymptotically tightly bounded by `g` up to constant factors.
-/
def ThetaBoundedBy (f g : Nat → Nat) : Prop :=
  EventuallyBoundedBy f g ∧ EventuallyBoundedBy g f

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

/-! ### Ω(n²) worst-case lower bound (CLRS §2.2) -/

/-- The closed-form formula for the triangular sum: {lit}`triangular n * 2 = n * (n + 1)`. -/
theorem triangular_eq_mul_two (n : Nat) : triangular n * 2 = n * (n + 1) := by
  induction n with
  | zero =>
      simp [triangular]
  | succ n ih =>
      simp [triangular]
      rw [add_mul, ih]
      nlinarith

/--
**Ω(n²) lower bound for the triangular sum** (CLRS §2.2 worst-case analysis).

For `n ≥ 2`, `triangular (n - 1) ≥ n² / 4`.  Reformulated as
`n² ≤ 4 · triangular (n - 1)` to stay in `Nat` arithmetic.

This is the key ingredient that, together with the quadratic upper bound
`insertionSortWorstComparisons_quadratic`, establishes the tight
Θ(n²) worst-case comparison count for insertion sort.
-/
theorem triangular_ge_quarter_square (n : Nat) (hn : 2 ≤ n) : n * n ≤ 4 * triangular (n - 1) := by
  have h_eq := triangular_eq_mul_two (n - 1)
  -- h_eq : triangular (n - 1) * 2 = (n - 1) * ((n - 1) + 1)
  -- Since n ≥ 2, (n - 1) + 1 = n
  have h_n_sub : (n - 1) + 1 = n := by omega
  have h_simp : triangular (n - 1) * 2 = (n - 1) * n := by
    rw [h_n_sub] at h_eq
    exact h_eq
  have h4 : 4 * triangular (n - 1) = 2 * ((n - 1) * n) := by
    calc
      4 * triangular (n - 1) = 2 * (2 * triangular (n - 1)) := by omega
      _ = 2 * (triangular (n - 1) * 2) := by rw [Nat.mul_comm 2 (triangular (n - 1))]
      _ = 2 * ((n - 1) * n) := by rw [h_simp]
  rw [h4]
  have h_bound : n ≤ 2 * (n - 1) := by omega
  have : n * n ≤ (2 * (n - 1)) * n := Nat.mul_le_mul h_bound (le_refl n)
  simpa [Nat.mul_assoc] using this

/-- The Ω(n²) lower bound for the worst-case comparison count of insertion sort. -/
theorem insertionSortWorstComparisons_quadratic_lower (n : Nat) (hn : 2 ≤ n) :
    n * n ≤ 4 * insertionSortWorstComparisons n := by
  unfold insertionSortWorstComparisons
  exact triangular_ge_quarter_square n hn

/-- The worst-case comparison count of insertion sort is Ω(n²). -/
theorem insertionSortWorstComparisons_eventually_quadratic_lower :
    EventuallyBoundedBy (fun n => n * n) insertionSortWorstComparisons := by
  refine ⟨4, 2, by decide, ?_⟩
  intro n hn
  exact insertionSortWorstComparisons_quadratic_lower n hn

/--
**Θ(n²) worst-case bound for insertion sort** (CLRS §2.2).

The tight asymptotic bound is obtained by combining the O(n²) upper bound
`insertionSortWorstComparisons_eventually_quadratic` with the Ω(n²) lower bound
`insertionSortWorstComparisons_eventually_quadratic_lower`.
-/
theorem insertionSortWorstComparisons_theta_quadratic :
    ThetaBoundedBy insertionSortWorstComparisons (fun n => n * n) := by
  refine ⟨insertionSortWorstComparisons_eventually_quadratic,
           insertionSortWorstComparisons_eventually_quadratic_lower⟩

/-! ### Best-case analysis (CLRS §2.2, eq. (2.1)) -/

/-- The number of comparisons made by `insertSorted x xs`. -/
def insertSortedComparisons (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => 1 + (if x ≤ y then 0 else insertSortedComparisons x ys)

/-- The number of comparisons made by `insertionSort xs`. -/
def insertionSortComparisons : List Nat → Nat
  | [] => 0
  | x :: xs => insertSortedComparisons x (insertionSort xs) + insertionSortComparisons xs

/-! ### Attained worst-case count of actual comparison runs -/

/-- Inserting into a list makes at most one comparison per existing element. -/
theorem insertSortedComparisons_le_length (x : Nat) (xs : List Nat) :
    insertSortedComparisons x xs ≤ xs.length := by
  induction xs with
  | nil => simp [insertSortedComparisons]
  | cons y ys ih =>
      simp only [insertSortedComparisons, List.length_cons]
      split <;> omega

/-- The triangular worst-case budget grows by the previous input length. -/
theorem insertionSortWorstComparisons_succ (n : Nat) :
    insertionSortWorstComparisons (n + 1) =
      n + insertionSortWorstComparisons n := by
  cases n with
  | zero => simp [insertionSortWorstComparisons, triangular]
  | succ n => simp [insertionSortWorstComparisons, triangular]; omega

/-- Every actual insertion-sort comparison count is bounded by the size budget. -/
theorem insertionSortComparisons_le_worst (xs : List Nat) :
    insertionSortComparisons xs ≤ insertionSortWorstComparisons xs.length := by
  induction xs with
  | nil => simp [insertionSortComparisons, insertionSortWorstComparisons, triangular]
  | cons x xs ih =>
      have h := insertSortedComparisons_le_length x (insertionSort xs)
      have hlen := (insertionSort_perm xs).length_eq
      rw [insertionSortComparisons, List.length_cons, insertionSortWorstComparisons_succ]
      omega

/-- An explicit worst-case family: the distinct keys n-1, ..., 0. -/
def insertionSortWorstInput : Nat → List Nat
  | 0 => []
  | n + 1 => n :: insertionSortWorstInput n

@[simp] theorem insertionSortWorstInput_length (n : Nat) :
    (insertionSortWorstInput n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [insertionSortWorstInput, ih]

private theorem mem_insertionSortWorstInput_lt {n x : Nat}
    (hx : x ∈ insertionSortWorstInput n) : x < n := by
  induction n with
  | zero => simp [insertionSortWorstInput] at hx
  | succ n ih =>
      simp only [insertionSortWorstInput, List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · exact Nat.lt_succ_of_lt (ih hx)

/-- A key larger than every existing element forces a full insertion scan. -/
theorem insertSortedComparisons_eq_length_of_forall_lt (x : Nat) (xs : List Nat)
    (h : ∀ y ∈ xs, y < x) : insertSortedComparisons x xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      have hxy : ¬x ≤ y := Nat.not_le.mpr (h y (by simp))
      have htail : ∀ z ∈ ys, z < x := fun z hz => h z (by simp [hz])
      simp [insertSortedComparisons, hxy, ih htail, Nat.add_comm]

/-- The descending family attains the worst-case budget at every size. -/
theorem insertionSortComparisons_worst_input (n : Nat) :
    insertionSortComparisons (insertionSortWorstInput n) =
      insertionSortWorstComparisons n := by
  induction n with
  | zero => simp [insertionSortWorstInput, insertionSortComparisons,
      insertionSortWorstComparisons, triangular]
  | succ n ih =>
      have hall : ∀ y ∈ insertionSort (insertionSortWorstInput n), y < n := by
        intro y hy
        exact mem_insertionSortWorstInput_lt
          ((insertionSort_perm (insertionSortWorstInput n)).mem_iff.mp hy)
      have hscan := insertSortedComparisons_eq_length_of_forall_lt n
        (insertionSort (insertionSortWorstInput n)) hall
      have hlen := (insertionSort_perm (insertionSortWorstInput n)).length_eq
      rw [insertionSortWorstInput, insertionSortComparisons, hscan, hlen,
        insertionSortWorstInput_length, ih, insertionSortWorstComparisons_succ]

/-- The size formula is the attained maximum of actual length-n run counts. -/
theorem insertionSortWorstComparisons_isGreatest (n : Nat) : IsGreatest
    {c | ∃ xs : List Nat, xs.length = n ∧ insertionSortComparisons xs = c}
    (insertionSortWorstComparisons n) := by
  constructor
  · exact ⟨insertionSortWorstInput n, insertionSortWorstInput_length n,
      insertionSortComparisons_worst_input n⟩
  · rintro c ⟨xs, hlen, rfl⟩
    simpa [hlen] using insertionSortComparisons_le_worst xs

/-- Actual worst-case comparison counts have the proved quadratic Theta bound. -/
theorem insertionSortComparisons_worst_case_theta :
    (∀ n, IsGreatest
      {c | ∃ xs : List Nat, xs.length = n ∧ insertionSortComparisons xs = c}
      (insertionSortWorstComparisons n)) ∧
    ThetaBoundedBy insertionSortWorstComparisons (fun n => n * n) :=
  ⟨insertionSortWorstComparisons_isGreatest,
    insertionSortWorstComparisons_theta_quadratic⟩


lemma allLe_of_perm {x : Nat} {xs ys : List Nat} (h_perm : xs.Perm ys) (h_allLe : AllLe x xs) :
    AllLe x ys := by
  intro y hy
  have hy' : y ∈ xs := h_perm.symm.mem_iff.mp hy
  exact h_allLe y hy'

/--
**Best-case comparison count for insertion sort** (CLRS eq. (2.1)).

When the input list is already sorted, insertion sort makes exactly `n - 1`
comparisons, where `n` is the length of the input.  This is the linear best
case described in the textbook.
-/
theorem insertionSortComparisons_best_case (xs : List Nat) (h_ordered : Ordered xs) :
    insertionSortComparisons xs = xs.length - 1 := by
  induction xs with
  | nil =>
      simp [insertionSortComparisons]
  | cons x xs ih =>
      have h_tail : Ordered xs := ordered_tail h_ordered
      have h_allLe : AllLe x xs := ordered_allLe_tail h_ordered
      have h_perm : (insertionSort xs).Perm xs := insertionSort_perm xs
      have h_allLe_sorted : AllLe x (insertionSort xs) :=
        allLe_of_perm h_perm.symm h_allLe
      have ih_eq := ih h_tail
      have h_len_perm : (insertionSort xs).length = xs.length := List.Perm.length_eq h_perm
      rw [insertionSortComparisons, List.length_cons, ih_eq]
      -- Goal: insertSortedComparisons x (insertionSort xs) + (xs.length - 1) = xs.length
      rcases h_ins : insertionSort xs with _ | ⟨y, ys⟩
      · -- insertionSort xs = []
        have h_len0 : xs.length = 0 := by
          simpa [h_ins] using h_len_perm.symm
        simp [insertSortedComparisons, h_len0]
      · -- insertionSort xs = y :: ys
        have h_mem : y ∈ (y :: ys) := by simp
        have h_allLe' : AllLe x (y :: ys) := by rwa [h_ins] at h_allLe_sorted
        have h_le : x ≤ y := h_allLe' y h_mem
        simp [insertSortedComparisons, h_le]
        have h_len_pos : 1 ≤ xs.length := by
          rw [h_ins] at h_len_perm
          simp at h_len_perm
          omega
        omega

/-- The best-case comparison count as a function of input size `n` (CLRS eq. (2.1)). -/
def insertionSortBestComparisons (n : Nat) : Nat := n - 1

theorem insertionSortBestComparisons_eventually_linear_upper :
    EventuallyBoundedBy insertionSortBestComparisons (fun n => n) := by
  refine ⟨1, 0, by decide, ?_⟩
  intro n _hn
  unfold insertionSortBestComparisons
  simpa [Nat.one_mul] using Nat.sub_le n 1

theorem insertionSortBestComparisons_eventually_linear_lower_aux (n : Nat) (hn : 2 ≤ n) : n ≤ 2 * (n - 1) := by
  omega

theorem insertionSortBestComparisons_eventually_linear_lower :
    EventuallyBoundedBy (fun n => n) insertionSortBestComparisons := by
  refine ⟨2, 2, by decide, ?_⟩
  intro n hn
  unfold insertionSortBestComparisons
  exact insertionSortBestComparisons_eventually_linear_lower_aux n hn

/--
**Θ(n) best-case bound for insertion sort** (CLRS eq. (2.1)).

The tight asymptotic bound is obtained by combining the O(n) upper bound
`insertionSortBestComparisons_eventually_linear_upper` with the Ω(n) lower bound
`insertionSortBestComparisons_eventually_linear_lower`.
-/
theorem insertionSortBestComparisons_theta_linear :
    ThetaBoundedBy insertionSortBestComparisons (fun n => n) := by
  refine ⟨insertionSortBestComparisons_eventually_linear_upper,
           insertionSortBestComparisons_eventually_linear_lower⟩

end Chapter02
end CLRS
