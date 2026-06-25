import Mathlib
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort

/-!
# CLRS Section 8.2 - Counting sort count-table refinement

This file adds the count-table layer that sits between the stable bucket
specification of {lit}`countingSortBy` and the array implementation in CLRS
{lit}`COUNTING-SORT`.

The point of this layer is deliberately modest and proof-friendly:

* {lit}`countTable` records the length of each stable bucket;
* {lit}`cumulativeCounts` records prefix-count boundaries;
* {lit}`countingSortByTable` uses the count table to drive the same emitted key
  range as {lit}`countingSortBy`;
* the table-driven wrapper is proved equal to the existing stable bucket
  specification, so it inherits orderedness, stability, membership, and
  permutation correctness.

The remaining imperative refinement is to prove the reverse scan that writes
into an output array with mutable cumulative counters.
-/

namespace CLRS
namespace Chapter08

/-! ## Count table certificates -/

/-- Count table entry {lit}`k` is the length of the stable input bucket for key {lit}`k`. -/
def countTable (key : α → Nat) (xs : List α) (maxKey : Nat) : Array Nat :=
  ((List.range (maxKey + 1)).map fun k => (bucket key xs k).length).toArray

/-- The count table is exactly the list of bucket lengths for keys {lit}`0..maxKey`. -/
theorem countTable_toList (key : α → Nat) (xs : List α) (maxKey : Nat) :
    (countTable key xs maxKey).toList =
      (List.range (maxKey + 1)).map fun k => (bucket key xs k).length := by
  simp [countTable]

/-- The count table has one slot for every key {lit}`0..maxKey`. -/
theorem countTable_size (key : α → Nat) (xs : List α) (maxKey : Nat) :
    (countTable key xs maxKey).size = maxKey + 1 := by
  simp [countTable]

/-- Summing the count table gives the length of the bucket-specification output. -/
theorem countTable_sum_eq_countingSortBy_length
    (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (countTable key xs maxKey).toList.sum =
      (countingSortBy maxKey key xs).length := by
  simp [countTable, countingSortBy, List.length_flatMap]

/-! ## Cumulative-count boundaries -/

/--
Prefix sums of a count table.  For counts {lit}`[c0, c1, ...]`, this returns
{lit}`[c0, c0 + c1, ...]`, matching the cumulative array in CLRS.
-/
def cumulativeCounts : List Nat → List Nat
  | [] => []
  | c :: cs => c :: (cumulativeCounts cs).map (fun n => c + n)

/-- Cumulative counts preserve the number of table slots. -/
theorem cumulativeCounts_length (counts : List Nat) :
    (cumulativeCounts counts).length = counts.length := by
  induction counts with
  | nil =>
      simp [cumulativeCounts]
  | cons c counts ih =>
      simp [cumulativeCounts, ih]

/-- The empty count table has no cumulative boundaries. -/
theorem cumulativeCounts_nil :
    cumulativeCounts ([] : List Nat) = [] := rfl

/-- The first cumulative boundary is the first count; later boundaries are shifted by it. -/
theorem cumulativeCounts_cons (c : Nat) (counts : List Nat) :
    cumulativeCounts (c :: counts) =
      c :: (cumulativeCounts counts).map (fun n => c + n) := rfl

/-- Cumulative counts for the counting-sort table have one slot per key. -/
def cumulativeCountTable (key : α → Nat) (xs : List α) (maxKey : Nat) : List Nat :=
  cumulativeCounts (countTable key xs maxKey).toList

theorem cumulativeCountTable_length (key : α → Nat) (xs : List α) (maxKey : Nat) :
    (cumulativeCountTable key xs maxKey).length = maxKey + 1 := by
  simp [cumulativeCountTable, cumulativeCounts_length, countTable_size]

/-! ## Table-driven wrapper -/

/--
Counting sort driven by the count-table size.

This is still a pure bucket specification, but the emitted key range now comes
from the count table, matching the first table-building phase of CLRS
{lit}`COUNTING-SORT`.
-/
def countingSortByTable (maxKey : Nat) (key : α → Nat) (xs : List α) : List α :=
  (List.range (countTable key xs maxKey).size).flatMap (bucket key xs)

/-- The count-table wrapper is extensionally the existing stable bucket sort. -/
theorem countingSortByTable_eq_countingSortBy
    (maxKey : Nat) (key : α → Nat) (xs : List α) :
    countingSortByTable maxKey key xs = countingSortBy maxKey key xs := by
  simp [countingSortByTable, countTable_size, countingSortBy]

theorem countingSortByTable_ordered (maxKey : Nat) (key : α → Nat) (xs : List α) :
    OrderedBy key (countingSortByTable maxKey key xs) := by
  rw [countingSortByTable_eq_countingSortBy]
  exact countingSortBy_ordered maxKey key xs

theorem countingSortByTable_bucket_eq
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (k : Nat) :
    bucket key (countingSortByTable maxKey key xs) k = bucket key xs k := by
  rw [countingSortByTable_eq_countingSortBy]
  exact countingSortBy_bucket_eq maxKey key xs hxs k

theorem countingSortByTable_mem_iff
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (x : α) :
    x ∈ countingSortByTable maxKey key xs ↔ x ∈ xs := by
  rw [countingSortByTable_eq_countingSortBy]
  exact countingSortBy_mem_iff maxKey key xs hxs x

theorem countingSortByTable_perm [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    (countingSortByTable maxKey key xs).Perm xs := by
  rw [countingSortByTable_eq_countingSortBy]
  exact countingSortBy_perm maxKey key xs hxs

/-- Reader-facing correctness theorem for the count-table refinement layer. -/
theorem countingSortByTable_correct [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    OrderedBy key (countingSortByTable maxKey key xs) ∧
      (∀ k, bucket key (countingSortByTable maxKey key xs) k = bucket key xs k) ∧
      (∀ x, x ∈ countingSortByTable maxKey key xs ↔ x ∈ xs) ∧
      (countingSortByTable maxKey key xs).Perm xs :=
  ⟨countingSortByTable_ordered maxKey key xs,
    countingSortByTable_bucket_eq maxKey key xs hxs,
    countingSortByTable_mem_iff maxKey key xs hxs,
    countingSortByTable_perm maxKey key xs hxs⟩

end Chapter08
end CLRS
