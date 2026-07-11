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
* {lit}`reverseBucket` models the right-to-left scan for one key by folding from
  the right and prepending matching elements;
* the table-driven and reverse-bucket wrappers are proved equal to the existing
  stable bucket specification, so they inherit orderedness, stability,
  membership, and permutation correctness.

The remaining imperative refinement is to replace the per-key reverse-bucket
view with a single mutable output array and mutable cumulative counters.
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

/-! ## Reverse-scan bucket refinement -/

namespace ReverseScan

/--
Build the stable bucket for one key by scanning from right to left and
prepending each matching element.

This is the one-key functional core of CLRS {lit}`COUNTING-SORT`'s final loop:
placing from the right side of a key segment is equivalent to a right fold that
prepends matches into that segment.
-/
def reverseBucket (key : α → Nat) (xs : List α) (k : Nat) : List α :=
  xs.foldr (fun x acc => if key x == k then x :: acc else acc) []

/-- The right-to-left bucket builder is exactly the stable input bucket. -/
theorem reverseBucket_eq_bucket (key : α → Nat) (xs : List α) (k : Nat) :
    reverseBucket key xs k = bucket key xs k := by
  unfold reverseBucket bucket
  rw [List.filter_eq_foldr]
  simp [Bool.cond_eq_ite]

theorem mem_reverseBucket_iff {key : α → Nat} {xs : List α} {k : Nat} {x : α} :
    x ∈ reverseBucket key xs k ↔ x ∈ xs ∧ key x = k := by
  rw [reverseBucket_eq_bucket]
  exact mem_bucket_iff

/--
Counting sort via per-key reverse buckets.

This is not yet the single mutable output array of CLRS, but it captures the
stability-critical reverse-scan behavior for every key segment.
-/
def countingSortByReverse (maxKey : Nat) (key : α → Nat) (xs : List α) : List α :=
  (List.range (maxKey + 1)).flatMap (reverseBucket key xs)

/-- The reverse-scan bucket wrapper is extensionally the count-table wrapper. -/
theorem countingSortByReverse_eq_countingSortByTable
    (maxKey : Nat) (key : α → Nat) (xs : List α) :
    countingSortByReverse maxKey key xs = countingSortByTable maxKey key xs := by
  rw [countingSortByTable_eq_countingSortBy]
  unfold countingSortByReverse countingSortBy
  apply List.flatMap_congr
  intro k _hk
  exact reverseBucket_eq_bucket key xs k

theorem countingSortByReverse_ordered (maxKey : Nat) (key : α → Nat) (xs : List α) :
    OrderedBy key (countingSortByReverse maxKey key xs) := by
  rw [countingSortByReverse_eq_countingSortByTable]
  exact countingSortByTable_ordered maxKey key xs

theorem countingSortByReverse_bucket_eq
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (k : Nat) :
    bucket key (countingSortByReverse maxKey key xs) k = bucket key xs k := by
  rw [countingSortByReverse_eq_countingSortByTable]
  exact countingSortByTable_bucket_eq maxKey key xs hxs k

theorem countingSortByReverse_mem_iff
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (x : α) :
    x ∈ countingSortByReverse maxKey key xs ↔ x ∈ xs := by
  rw [countingSortByReverse_eq_countingSortByTable]
  exact countingSortByTable_mem_iff maxKey key xs hxs x

theorem countingSortByReverse_perm [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    (countingSortByReverse maxKey key xs).Perm xs := by
  rw [countingSortByReverse_eq_countingSortByTable]
  exact countingSortByTable_perm maxKey key xs hxs

/-- Reader-facing correctness theorem for the reverse-scan bucket refinement. -/
theorem countingSortByReverse_correct [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    OrderedBy key (countingSortByReverse maxKey key xs) ∧
      (∀ k, bucket key (countingSortByReverse maxKey key xs) k = bucket key xs k) ∧
      (∀ x, x ∈ countingSortByReverse maxKey key xs ↔ x ∈ xs) ∧
      (countingSortByReverse maxKey key xs).Perm xs :=
  ⟨countingSortByReverse_ordered maxKey key xs,
    countingSortByReverse_bucket_eq maxKey key xs hxs,
    countingSortByReverse_mem_iff maxKey key xs hxs,
    countingSortByReverse_perm maxKey key xs hxs⟩

/-! ## Cumulative segment counts -/

/-- Number of elements in the leading key segments {lit}`0..k`. -/
def cumulativeCount (key : α → Nat) (xs : List α) (k : Nat) : Nat :=
  ((List.range (k + 1)).map fun i => (bucket key xs i).length).sum

theorem cumulativeCount_zero (key : α → Nat) (xs : List α) :
    cumulativeCount key xs 0 = (bucket key xs 0).length := by
  simp [cumulativeCount]

/--
The cumulative segment count grows by exactly the next stable bucket length.
-/
theorem cumulativeCount_succ (key : α → Nat) (xs : List α) (k : Nat) :
    cumulativeCount key xs (k + 1) =
      cumulativeCount key xs k + (bucket key xs (k + 1)).length := by
  simp [cumulativeCount, List.range_succ, add_assoc]

/-- Cumulative segment count at {lit}`maxKey` is the counting-sort output length. -/
theorem cumulativeCount_eq_countingSortBy_length
    (maxKey : Nat) (key : α → Nat) (xs : List α) :
    cumulativeCount key xs maxKey = (countingSortBy maxKey key xs).length := by
  simp [cumulativeCount, countingSortBy, List.length_flatMap]

/-- The reverse-scan wrapper has the same length as the cumulative final boundary. -/
theorem countingSortByReverse_length
    (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (countingSortByReverse maxKey key xs).length =
      cumulativeCount key xs maxKey := by
  rw [countingSortByReverse_eq_countingSortByTable,
    countingSortByTable_eq_countingSortBy,
    cumulativeCount_eq_countingSortBy_length]

end ReverseScan

end Chapter08
end CLRS
