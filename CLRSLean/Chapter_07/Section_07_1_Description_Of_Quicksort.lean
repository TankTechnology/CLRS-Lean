import Mathlib

/-!
# CLRS Section 7.1 - Description of quicksort

This file starts the Chapter 7 sorting track with a Lean-friendly functional
model of quicksort and a scan-state proof spine for the CLRS partition loop.
The theorem layer proves the same mathematical facts used by the textbook
proof:

* partition returns exactly the original tail elements;
* the left partition contains only elements at most the pivot;
* the right partition contains only elements greater than the pivot;
* the scan-state partition loop preserves its exact invariant and computes the
  same regions as the specification partition;
* an array-facing wrapper returns a pivot index whose prefix/suffix satisfy the
  CLRS partition postcondition;
* functional quicksort returns an ordered permutation of the input.

The remaining array-level strengthening target is to refine this proof to a
swap trace over a mutable array-segment model.  Randomized/expected-time
analysis is also separate.
-/

namespace CLRS
namespace Chapter07

/-! ## Ordered lists and pivot bounds -/

/-- A compact sortedness predicate for lists of natural numbers. -/
def Ordered : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x ≤ y ∧ Ordered (y :: ys)

/-- Every element of {lit}`xs` is at least {lit}`lower`. -/
def AllLe (lower : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, lower ≤ x

/-- Every element of {lit}`xs` is at most {lit}`upper`. -/
def AllLeUpper (xs : List Nat) (upper : Nat) : Prop :=
  ∀ x ∈ xs, x ≤ upper

/-- Every element of {lit}`xs` is strictly greater than {lit}`lower`. -/
def AllGt (lower : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, lower < x

theorem ordered_tail {x : Nat} {xs : List Nat}
    (h : Ordered (x :: xs)) : Ordered xs := by
  cases xs with
  | nil =>
      trivial
  | cons _ _ =>
      exact h.2

theorem ordered_allLe_tail {x : Nat} {xs : List Nat}
    (h : Ordered (x :: xs)) : AllLe x xs := by
  induction xs generalizing x with
  | nil =>
      intro y hy
      simp at hy
  | cons y ys ih =>
      intro z hz
      simp at hz
      rcases hz with rfl | hz
      · exact h.1
      · exact Nat.le_trans h.1 (ih h.2 z hz)

theorem ordered_cons_of_allLe {x : Nat} {xs : List Nat}
    (hxs : Ordered xs) (hall : AllLe x xs) : Ordered (x :: xs) := by
  cases xs with
  | nil =>
      trivial
  | cons y ys =>
      exact ⟨hall y (by simp), hxs⟩

/-- Bounds survive permutation. -/
theorem allLeUpper_of_perm {xs ys : List Nat} {upper : Nat}
    (hperm : xs.Perm ys) (hys : AllLeUpper ys upper) :
    AllLeUpper xs upper := by
  intro x hx
  exact hys x (hperm.mem_iff.mp hx)

/-- Strict lower bounds survive permutation. -/
theorem allGt_of_perm {xs ys : List Nat} {lower : Nat}
    (hperm : xs.Perm ys) (hys : AllGt lower ys) :
    AllGt lower xs := by
  intro x hx
  exact hys x (hperm.mem_iff.mp hx)

/--
If the left list is sorted and bounded by the pivot, and the right list is
sorted and strictly above the pivot, then the quicksort concatenation is sorted.
-/
theorem ordered_append_pivot {left right : List Nat} {pivot : Nat}
    (hleft : Ordered left) (hright : Ordered right)
    (hle : AllLeUpper left pivot) (hgt : AllGt pivot right) :
    Ordered (left ++ pivot :: right) := by
  induction left with
  | nil =>
      have hp_right : AllLe pivot right := by
        intro x hx
        exact Nat.le_of_lt (hgt x hx)
      simpa using ordered_cons_of_allLe hright hp_right
  | cons x xs ih =>
      have hxs : Ordered xs := ordered_tail hleft
      have hle_x : x ≤ pivot := hle x (by simp)
      have hle_xs : AllLeUpper xs pivot := by
        intro y hy
        exact hle y (by simp [hy])
      have htail : Ordered (xs ++ pivot :: right) := ih hxs hle_xs
      have hbound_tail : AllLe x (xs ++ pivot :: right) := by
        intro y hy
        simp at hy
        rcases hy with hyxs | hy_pivot | hyright
        · exact ordered_allLe_tail hleft y hyxs
        · simpa [hy_pivot] using hle_x
        · exact Nat.le_trans hle_x (Nat.le_of_lt (hgt y hyright))
      simpa using ordered_cons_of_allLe htail hbound_tail

/-! ## Partition around a pivot -/

/--
Stable partition around a pivot.  The first component contains elements
{lit}`≤ p`; the second component contains elements {lit}`> p`.
-/
def partitionAround (p : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
      let parts := partitionAround p xs
      if x ≤ p then
        (x :: parts.1, parts.2)
      else
        (parts.1, x :: parts.2)

/-- The left partition contains only elements at most the pivot. -/
theorem partitionAround_left_allLeUpper (p : Nat) (xs : List Nat) :
    AllLeUpper (partitionAround p xs).1 p := by
  induction xs with
  | nil =>
      intro x hx
      simp [partitionAround] at hx
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · intro y hy
        simp [partitionAround, hxle] at hy
        rcases hy with rfl | hy
        · exact hxle
        · exact ih y hy
      · intro y hy
        simp [partitionAround, hxle] at hy
        exact ih y hy

/-- The right partition contains only elements strictly greater than the pivot. -/
theorem partitionAround_right_allGt (p : Nat) (xs : List Nat) :
    AllGt p (partitionAround p xs).2 := by
  induction xs with
  | nil =>
      intro x hx
      simp [partitionAround] at hx
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · intro y hy
        simp [partitionAround, hxle] at hy
        exact ih y hy
      · have hpx : p < x := Nat.lt_of_not_ge hxle
        intro y hy
        simp [partitionAround, hxle] at hy
        rcases hy with rfl | hy
        · exact hpx
        · exact ih y hy

/-- The left partition is no longer than the input tail. -/
theorem partitionAround_left_length_le (p : Nat) (xs : List Nat) :
    (partitionAround p xs).1.length ≤ xs.length := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · simp [partitionAround, hxle]
        exact ih
      · simp [partitionAround, hxle]
        exact Nat.le_trans ih (Nat.le_succ xs.length)

/-- The right partition is no longer than the input tail. -/
theorem partitionAround_right_length_le (p : Nat) (xs : List Nat) :
    (partitionAround p xs).2.length ≤ xs.length := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · simp [partitionAround, hxle]
        exact Nat.le_trans ih (Nat.le_succ xs.length)
      · simp [partitionAround, hxle]
        exact ih

/-- Moving an element from the middle of an append to the front preserves elements. -/
theorem perm_append_cons (x : Nat) (left right : List Nat) :
    (left ++ x :: right).Perm (x :: left ++ right) := by
  induction left with
  | nil =>
      simp
  | cons y ys ih =>
      exact (List.Perm.cons y ih).trans (List.Perm.swap x y (ys ++ right))

/-- Partition returns exactly the input elements, just split by the pivot test. -/
theorem partitionAround_perm (p : Nat) (xs : List Nat) :
    ((partitionAround p xs).1 ++ (partitionAround p xs).2).Perm xs := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hxle : x ≤ p
      · simpa [partitionAround, hxle] using List.Perm.cons x ih
      · have hmiddle :
            ((partitionAround p xs).1 ++ x :: (partitionAround p xs).2).Perm
              (x :: (partitionAround p xs).1 ++ (partitionAround p xs).2) :=
          perm_append_cons x (partitionAround p xs).1 (partitionAround p xs).2
        exact by
          simpa [partitionAround, hxle] using hmiddle.trans (List.Perm.cons x ih)

/-- The left partition is exactly the stable filter of elements at most the pivot. -/
theorem partitionAround_left_eq_filter (p : Nat) (xs : List Nat) :
    (partitionAround p xs).1 = xs.filter (fun x => decide (x ≤ p)) := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hx : x ≤ p
      · simp [partitionAround, hx, ih]
      · simp [partitionAround, hx, ih]

/-- The right partition is exactly the stable filter of elements greater than the pivot. -/
theorem partitionAround_right_eq_filter (p : Nat) (xs : List Nat) :
    (partitionAround p xs).2 = xs.filter (fun x => decide (p < x)) := by
  induction xs with
  | nil =>
      simp [partitionAround]
  | cons x xs ih =>
      by_cases hx : x ≤ p
      · have hnlt : ¬ p < x := not_lt_of_ge hx
        simp [partitionAround, hx, hnlt, ih]
      · have hlt : p < x := Nat.lt_of_not_ge hx
        simp [partitionAround, hx, hlt, ih]

/-- Membership characterization for the left partition. -/
theorem mem_partitionAround_left_iff (p : Nat) (xs : List Nat) (x : Nat) :
    x ∈ (partitionAround p xs).1 ↔ x ∈ xs ∧ x ≤ p := by
  rw [partitionAround_left_eq_filter]
  simp

/-- Membership characterization for the right partition. -/
theorem mem_partitionAround_right_iff (p : Nat) (xs : List Nat) (x : Nat) :
    x ∈ (partitionAround p xs).2 ↔ x ∈ xs ∧ p < x := by
  rw [partitionAround_right_eq_filter]
  simp

/--
Reader-facing correctness theorem for stable partition around a pivot.

It packages the facts used by the quicksort proof: the left side contains
exactly the input elements at most the pivot, the right side contains exactly
the input elements greater than the pivot, and concatenating the two sides is a
permutation of the original input tail.
-/
theorem partitionAround_correct (p : Nat) (xs : List Nat) :
    AllLeUpper (partitionAround p xs).1 p ∧
      AllGt p (partitionAround p xs).2 ∧
      ((partitionAround p xs).1 ++ (partitionAround p xs).2).Perm xs ∧
      (∀ x, x ∈ (partitionAround p xs).1 ↔ x ∈ xs ∧ x ≤ p) ∧
      (∀ x, x ∈ (partitionAround p xs).2 ↔ x ∈ xs ∧ p < x) :=
  ⟨partitionAround_left_allLeUpper p xs,
    partitionAround_right_allGt p xs,
    partitionAround_perm p xs,
    mem_partitionAround_left_iff p xs,
    mem_partitionAround_right_iff p xs⟩

/-! ## A CLRS partition-loop proof spine -/

/--
State for a Lean-friendly model of the CLRS {lit}`PARTITION` loop.

The loop scans the tail from left to right.  The {lit}`low` region contains
processed elements known to be at most the pivot; the {lit}`high` region
contains processed elements known to be greater than the pivot.
-/
structure PartitionLoopState where
  /-- Processed elements that belong on the left of the pivot. -/
  low : List Nat
  /-- Processed elements that belong on the right of the pivot. -/
  high : List Nat

/--
Exact loop invariant for the scan model: after processing {lit}`seen`, the
two regions are exactly the stable filters of {lit}`seen`.
-/
def PartitionLoopInvariant (p : Nat) (seen : List Nat)
    (state : PartitionLoopState) : Prop :=
  state.low = seen.filter (fun x => decide (x ≤ p)) ∧
    state.high = seen.filter (fun x => decide (p < x))

/-- One CLRS-style partition-loop step for a newly scanned element. -/
def partitionLoopStep (p : Nat) (state : PartitionLoopState)
    (x : Nat) : PartitionLoopState :=
  if x ≤ p then
    { low := state.low ++ [x], high := state.high }
  else
    { low := state.low, high := state.high ++ [x] }

/-- Run the partition loop from an arbitrary processed-prefix state. -/
def partitionLoopFrom (p : Nat) :
    PartitionLoopState → List Nat → PartitionLoopState
  | state, [] => state
  | state, x :: xs => partitionLoopFrom p (partitionLoopStep p state x) xs

/-- Run the partition loop on an input tail from the empty state. -/
def partitionLoop (p : Nat) (xs : List Nat) : PartitionLoopState :=
  partitionLoopFrom p { low := [], high := [] } xs

/-- The exact invariant is preserved by one partition-loop step. -/
theorem partitionLoopStep_invariant (p : Nat) (seen : List Nat)
    (state : PartitionLoopState) (x : Nat)
    (hinv : PartitionLoopInvariant p seen state) :
    PartitionLoopInvariant p (seen ++ [x]) (partitionLoopStep p state x) := by
  rcases hinv with ⟨hlow, hhigh⟩
  by_cases hx : x ≤ p
  · have hnlt : ¬ p < x := not_lt_of_ge hx
    simp [PartitionLoopInvariant, partitionLoopStep, hx, hnlt, hlow, hhigh]
  · have hlt : p < x := Nat.lt_of_not_ge hx
    simp [PartitionLoopInvariant, partitionLoopStep, hx, hlt, hlow, hhigh]

/--
Running the loop over a remaining suffix preserves the exact invariant for the
whole processed prefix.
-/
theorem partitionLoopFrom_invariant (p : Nat) :
    ∀ (xs seen : List Nat) (state : PartitionLoopState),
      PartitionLoopInvariant p seen state →
        PartitionLoopInvariant p (seen ++ xs) (partitionLoopFrom p state xs)
  | [], seen, state, hinv => by
      simpa [partitionLoopFrom] using hinv
  | x :: xs, seen, state, hinv => by
      have hstep :
          PartitionLoopInvariant p (seen ++ [x])
            (partitionLoopStep p state x) :=
        partitionLoopStep_invariant p seen state x hinv
      have htail :
          PartitionLoopInvariant p ((seen ++ [x]) ++ xs)
            (partitionLoopFrom p (partitionLoopStep p state x) xs) :=
        partitionLoopFrom_invariant p xs (seen ++ [x])
          (partitionLoopStep p state x) hstep
      simpa [partitionLoopFrom, List.append_assoc] using htail

/-- The partition loop satisfies the exact invariant for the whole input. -/
theorem partitionLoop_invariant (p : Nat) (xs : List Nat) :
    PartitionLoopInvariant p xs (partitionLoop p xs) := by
  have hinit :
      PartitionLoopInvariant p ([] : List Nat) { low := [], high := [] } := by
    simp [PartitionLoopInvariant]
  have hrun := partitionLoopFrom_invariant p xs [] { low := [], high := [] } hinit
  simpa [partitionLoop] using hrun

/-- The loop's low region is the stable filter of elements at most the pivot. -/
theorem partitionLoop_low_eq_filter (p : Nat) (xs : List Nat) :
    (partitionLoop p xs).low = xs.filter (fun x => decide (x ≤ p)) :=
  (partitionLoop_invariant p xs).1

/-- The loop's high region is the stable filter of elements greater than the pivot. -/
theorem partitionLoop_high_eq_filter (p : Nat) (xs : List Nat) :
    (partitionLoop p xs).high = xs.filter (fun x => decide (p < x)) :=
  (partitionLoop_invariant p xs).2

/--
The loop model computes the same two regions as the specification partition
{lit}`partitionAround`.
-/
theorem partitionLoop_eq_partitionAround (p : Nat) (xs : List Nat) :
    (partitionLoop p xs).low = (partitionAround p xs).1 ∧
      (partitionLoop p xs).high = (partitionAround p xs).2 := by
  constructor
  · rw [partitionLoop_low_eq_filter, partitionAround_left_eq_filter]
  · rw [partitionLoop_high_eq_filter, partitionAround_right_eq_filter]

/-- The loop's low region contains only elements at most the pivot. -/
theorem partitionLoop_low_allLeUpper (p : Nat) (xs : List Nat) :
    AllLeUpper (partitionLoop p xs).low p := by
  rw [(partitionLoop_eq_partitionAround p xs).1]
  exact partitionAround_left_allLeUpper p xs

/-- The loop's high region contains only elements greater than the pivot. -/
theorem partitionLoop_high_allGt (p : Nat) (xs : List Nat) :
    AllGt p (partitionLoop p xs).high := by
  rw [(partitionLoop_eq_partitionAround p xs).2]
  exact partitionAround_right_allGt p xs

/-- The two loop regions contain exactly the scanned input elements. -/
theorem partitionLoop_perm (p : Nat) (xs : List Nat) :
    ((partitionLoop p xs).low ++ (partitionLoop p xs).high).Perm xs := by
  rw [(partitionLoop_eq_partitionAround p xs).1,
    (partitionLoop_eq_partitionAround p xs).2]
  exact partitionAround_perm p xs

/-- Membership characterization for the loop's low region. -/
theorem mem_partitionLoop_low_iff (p : Nat) (xs : List Nat) (x : Nat) :
    x ∈ (partitionLoop p xs).low ↔ x ∈ xs ∧ x ≤ p := by
  rw [(partitionLoop_eq_partitionAround p xs).1]
  exact mem_partitionAround_left_iff p xs x

/-- Membership characterization for the loop's high region. -/
theorem mem_partitionLoop_high_iff (p : Nat) (xs : List Nat) (x : Nat) :
    x ∈ (partitionLoop p xs).high ↔ x ∈ xs ∧ p < x := by
  rw [(partitionLoop_eq_partitionAround p xs).2]
  exact mem_partitionAround_right_iff p xs x

/--
Reader-facing correctness theorem for the CLRS-style partition loop.

It exposes the loop invariant's final consequences: low-side bounds, high-side
bounds, permutation preservation for the scanned tail, and membership
classification for both regions.
-/
theorem partitionLoop_correct (p : Nat) (xs : List Nat) :
    AllLeUpper (partitionLoop p xs).low p ∧
      AllGt p (partitionLoop p xs).high ∧
      ((partitionLoop p xs).low ++ (partitionLoop p xs).high).Perm xs ∧
      (∀ x, x ∈ (partitionLoop p xs).low ↔ x ∈ xs ∧ x ≤ p) ∧
      (∀ x, x ∈ (partitionLoop p xs).high ↔ x ∈ xs ∧ p < x) :=
  ⟨partitionLoop_low_allLeUpper p xs,
    partitionLoop_high_allGt p xs,
    partitionLoop_perm p xs,
    mem_partitionLoop_low_iff p xs,
    mem_partitionLoop_high_iff p xs⟩

/--
Partition result obtained by placing the pivot between the final low and high
regions.
-/
def clrsPartition (p : Nat) (xs : List Nat) : List Nat :=
  let state := partitionLoop p xs
  state.low ++ p :: state.high

/--
Reader-facing correctness theorem for the CLRS-style partition result.

The returned list is a permutation of the pivot followed by the scanned tail,
and the final low/high loop regions satisfy the usual partition bounds.
-/
theorem clrsPartition_correct (p : Nat) (xs : List Nat) :
    AllLeUpper (partitionLoop p xs).low p ∧
      AllGt p (partitionLoop p xs).high ∧
      ((partitionLoop p xs).low ++ (partitionLoop p xs).high).Perm xs ∧
      (clrsPartition p xs).Perm (p :: xs) ∧
      (∀ x, x ∈ (partitionLoop p xs).low ↔ x ∈ xs ∧ x ≤ p) ∧
      (∀ x, x ∈ (partitionLoop p xs).high ↔ x ∈ xs ∧ p < x) := by
  let state := partitionLoop p xs
  have hloop := partitionLoop_correct p xs
  have htail : (state.low ++ state.high).Perm xs := by
    simpa [state] using hloop.2.2.1
  have hmiddle : (state.low ++ p :: state.high).Perm
      (p :: state.low ++ state.high) :=
    perm_append_cons p state.low state.high
  have hwhole : (clrsPartition p xs).Perm (p :: xs) := by
    simpa [clrsPartition, state] using hmiddle.trans (List.Perm.cons p htail)
  exact ⟨hloop.1, hloop.2.1, hloop.2.2.1, hwhole, hloop.2.2.2.1,
    hloop.2.2.2.2⟩

/-! ## Array-facing partition result -/

/--
Array-facing result of partitioning around a pivot.

The list {lit}`out` is the post-partition array segment, and
{lit}`pivotIndex` is the index at which the pivot is placed.
-/
structure PartitionArrayResult where
  /-- Post-partition array segment. -/
  out : List Nat
  /-- Zero-based index of the pivot in {lit}`out`. -/
  pivotIndex : Nat

/--
Array-facing wrapper for the CLRS partition result.

This keeps the proof connected to the scan-state invariant while exposing the
ordinary array postcondition shape: a returned pivot index plus an output
segment.
-/
def clrsPartitionArray (p : Nat) (xs : List Nat) : PartitionArrayResult :=
  let state := partitionLoop p xs
  { out := state.low ++ p :: state.high, pivotIndex := state.low.length }

/-- The array-facing wrapper has the same output as {lit}`clrsPartition`. -/
theorem clrsPartitionArray_out (p : Nat) (xs : List Nat) :
    (clrsPartitionArray p xs).out = clrsPartition p xs := by
  simp [clrsPartitionArray, clrsPartition]

/-- The returned pivot index is in bounds. -/
theorem clrsPartitionArray_pivotIndex_lt (p : Nat) (xs : List Nat) :
    (clrsPartitionArray p xs).pivotIndex <
      (clrsPartitionArray p xs).out.length := by
  simp [clrsPartitionArray]

/-- The pivot is stored exactly at the returned index. -/
theorem clrsPartitionArray_pivot (p : Nat) (xs : List Nat) :
    (clrsPartitionArray p xs).out[(clrsPartitionArray p xs).pivotIndex]? =
      some p := by
  simp [clrsPartitionArray]

/-- The segment left of the returned index contains only values at most the pivot. -/
theorem clrsPartitionArray_left_bound (p : Nat) (xs : List Nat) :
    AllLeUpper
      ((clrsPartitionArray p xs).out.take
        (clrsPartitionArray p xs).pivotIndex) p := by
  simpa [clrsPartitionArray] using partitionLoop_low_allLeUpper p xs

/-- The segment right of the returned index contains only values greater than the pivot. -/
theorem clrsPartitionArray_right_bound (p : Nat) (xs : List Nat) :
    AllGt p
      ((clrsPartitionArray p xs).out.drop
        ((clrsPartitionArray p xs).pivotIndex + 1)) := by
  simpa [clrsPartitionArray] using partitionLoop_high_allGt p xs

/-- The array-facing partition output preserves exactly the input elements plus the pivot. -/
theorem clrsPartitionArray_perm (p : Nat) (xs : List Nat) :
    (clrsPartitionArray p xs).out.Perm (p :: xs) := by
  simpa [clrsPartitionArray_out] using (clrsPartition_correct p xs).2.2.2.1

/--
Reader-facing correctness theorem for the array-facing partition wrapper.

It packages the returned-index postcondition: the pivot is in bounds and stored
at the returned index; the prefix before it is at most the pivot; the suffix
after it is greater than the pivot; and the output is a permutation of the
pivot followed by the scanned tail.
-/
theorem clrsPartitionArray_correct (p : Nat) (xs : List Nat) :
    (clrsPartitionArray p xs).pivotIndex <
        (clrsPartitionArray p xs).out.length ∧
      (clrsPartitionArray p xs).out[(clrsPartitionArray p xs).pivotIndex]? =
        some p ∧
      AllLeUpper
        ((clrsPartitionArray p xs).out.take
          (clrsPartitionArray p xs).pivotIndex) p ∧
      AllGt p
        ((clrsPartitionArray p xs).out.drop
          ((clrsPartitionArray p xs).pivotIndex + 1)) ∧
      (clrsPartitionArray p xs).out.Perm (p :: xs) :=
  ⟨clrsPartitionArray_pivotIndex_lt p xs,
    clrsPartitionArray_pivot p xs,
    clrsPartitionArray_left_bound p xs,
    clrsPartitionArray_right_bound p xs,
    clrsPartitionArray_perm p xs⟩

/-! ## Functional quicksort -/

/--
Fuelled functional quicksort.  With fuel at least {lit}`xs.length`, the
recursive calls have enough fuel for the partition tails.  The public
{lit}`quickSort` below uses exactly that amount of fuel.
-/
def quickSortFuel : Nat → List Nat → List Nat
  | 0, xs => xs
  | _ + 1, [] => []
  | fuel + 1, pivot :: xs =>
      let parts := partitionAround pivot xs
      quickSortFuel fuel parts.1 ++ pivot :: quickSortFuel fuel parts.2

/-- Functional quicksort over lists of natural numbers. -/
def quickSort (xs : List Nat) : List Nat :=
  quickSortFuel xs.length xs

/-- With enough fuel, quicksort preserves the input elements up to permutation. -/
theorem quickSortFuel_perm :
    ∀ (fuel : Nat) (xs : List Nat), xs.length ≤ fuel →
      (quickSortFuel fuel xs).Perm xs := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      simp [quickSortFuel, hnil]
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil =>
          simp [quickSortFuel]
      | cons pivot tail =>
          let parts := partitionAround pivot tail
          have htail_len : tail.length ≤ fuel := by
            exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
          have hleft_len : parts.1.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_left_length_le pivot tail) htail_len
          have hright_len : parts.2.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_right_length_le pivot tail) htail_len
          have hleft_perm : (quickSortFuel fuel parts.1).Perm parts.1 :=
            ih parts.1 hleft_len
          have hright_perm : (quickSortFuel fuel parts.2).Perm parts.2 :=
            ih parts.2 hright_len
          have hboth :
              (quickSortFuel fuel parts.1 ++ pivot :: quickSortFuel fuel parts.2).Perm
                (parts.1 ++ pivot :: parts.2) :=
            List.Perm.append hleft_perm (List.Perm.cons pivot hright_perm)
          have hmiddle : (parts.1 ++ pivot :: parts.2).Perm
              (pivot :: parts.1 ++ parts.2) :=
            perm_append_cons pivot parts.1 parts.2
          have hpartition : (parts.1 ++ parts.2).Perm tail := by
            simpa [parts] using partitionAround_perm pivot tail
          simpa [quickSortFuel, parts] using
            hboth.trans (hmiddle.trans (List.Perm.cons pivot hpartition))

/-- With enough fuel, quicksort returns an ordered list. -/
theorem quickSortFuel_ordered :
    ∀ (fuel : Nat) (xs : List Nat), xs.length ≤ fuel →
      Ordered (quickSortFuel fuel xs) := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs hlen
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      simp [quickSortFuel, hnil, Ordered]
  | succ fuel ih =>
      intro xs hlen
      cases xs with
      | nil =>
          simp [quickSortFuel, Ordered]
      | cons pivot tail =>
          let parts := partitionAround pivot tail
          have htail_len : tail.length ≤ fuel := by
            exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
          have hleft_len : parts.1.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_left_length_le pivot tail) htail_len
          have hright_len : parts.2.length ≤ fuel := by
            exact Nat.le_trans (partitionAround_right_length_le pivot tail) htail_len
          have hleft_ordered : Ordered (quickSortFuel fuel parts.1) :=
            ih parts.1 hleft_len
          have hright_ordered : Ordered (quickSortFuel fuel parts.2) :=
            ih parts.2 hright_len
          have hleft_perm : (quickSortFuel fuel parts.1).Perm parts.1 :=
            quickSortFuel_perm fuel parts.1 hleft_len
          have hright_perm : (quickSortFuel fuel parts.2).Perm parts.2 :=
            quickSortFuel_perm fuel parts.2 hright_len
          have hleft_bound : AllLeUpper (quickSortFuel fuel parts.1) pivot :=
            allLeUpper_of_perm hleft_perm
              (by simpa [parts] using partitionAround_left_allLeUpper pivot tail)
          have hright_bound : AllGt pivot (quickSortFuel fuel parts.2) :=
            allGt_of_perm hright_perm
              (by simpa [parts] using partitionAround_right_allGt pivot tail)
          simpa [quickSortFuel, parts] using
            ordered_append_pivot hleft_ordered hright_ordered hleft_bound hright_bound

/-- Quicksort preserves the input elements up to permutation. -/
theorem quickSort_perm (xs : List Nat) :
    (quickSort xs).Perm xs := by
  exact quickSortFuel_perm xs.length xs (Nat.le_refl xs.length)

/-- Quicksort returns an ordered list. -/
theorem quickSort_ordered (xs : List Nat) :
    Ordered (quickSort xs) := by
  exact quickSortFuel_ordered xs.length xs (Nat.le_refl xs.length)

/-- The reader-facing correctness theorem for the functional quicksort model. -/
theorem quickSort_correct (xs : List Nat) :
    Ordered (quickSort xs) ∧ (quickSort xs).Perm xs :=
  ⟨quickSort_ordered xs, quickSort_perm xs⟩

end Chapter07
end CLRS
