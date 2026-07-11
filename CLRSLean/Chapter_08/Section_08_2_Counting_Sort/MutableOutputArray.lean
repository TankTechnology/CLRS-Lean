import Mathlib
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.CountTables

/-!
# CLRS Section 8.2 - Counting sort mutable output-array refinement

This file adds the final imperative refinement layer for CLRS
{lit}`COUNTING-SORT`: a single mutable output {lit}`Array` filled by a
cumulative-count reverse scan.  It sits on top of the count-table and
reverse-scan layers of {lit}`Section_08_2_Counting_Sort.CountTables` and reuses
the concrete {lit}`Array` pattern established for the mutable dynamic tables of
CLRS Section 17.4.

The construction {lit}`countingSortArray` fills the output {lit}`Array α`
segment by segment for keys {lit}`0, 1, ..., maxKey`, appending each key segment
produced by the stability-preserving reverse scan
{lit}`ReverseScan.reverseBucket`.  The segment boundaries are exactly the
cumulative counts {lit}`ReverseScan.cumulativeCount`, matching the prefix-count
array {lit}`C` of the textbook algorithm: after filling keys {lit}`0..j` the
number of used output slots is {lit}`cumulativeCount key xs j`.

The refinement theorem {lit}`countingSortArray_toList` proves that the mutable
output array, read back as a list, is *extensionally equal* to the stable bucket
specification {lit}`countingSortBy`.  The array therefore inherits the full
correctness spine: ordered-by-key output, per-key stability, membership
preservation, and multiset permutation.  Finally {lit}`countingSortArrayCost`
records the four linear passes of the algorithm and
{lit}`countingSortArrayCost_bigO` packages the {lit}`O(n + k)` work bound, with
{lit}`countingSortArray_size_of_allKeysLe` pinning the number of scatter writes
to exactly {lit}`n` under the CLRS precondition that keys lie in {lit}`0..maxKey`.

Main results:

- Definition {lit}`countingSortArray`: mutable output-array counting sort.
- Definition {lit}`countingSortInPlace`: the same refinement taking and
  returning an {lit}`Array`.
- Theorem {lit}`countingSortArray_toList`: the mutable output array refines
  {lit}`countingSortBy` extensionally.
- Theorems {lit}`countingSortArray_ordered`, {lit}`countingSortArray_bucket_eq`,
  {lit}`countingSortArray_mem_iff`, {lit}`countingSortArray_perm`, and
  {lit}`countingSortArray_correct`: inherited ordered/stable/membership/permutation
  correctness.
- Theorems {lit}`scatter_range_size` and {lit}`countingSortArray_size`: the
  fill offsets are the cumulative counts.
- Theorem {lit}`countingSortArray_size_of_allKeysLe`: exactly {lit}`n` scatter
  writes under the CLRS key-range precondition.
- Definition {lit}`countingSortArrayCost` and theorems
  {lit}`countingSortArrayCost_eq`, {lit}`countingSortArrayCost_le`, and
  {lit}`countingSortArrayCost_bigO`: the linear {lit}`O(n + k)` work bound.

Notation conventions used in this section:

- `key` : the natural-number key function
- `xs`  : the input list
- `maxKey` : the maximum key `k`; keys are assumed to lie in `0..maxKey`
- `n`   : the input length `xs.length`

Current gaps:

- A full RAM/step-count operational cost semantics (charging individual array
  reads and writes through an execution model) remains out of scope; the linear
  work bound here is a per-pass step count matching the CLRS accounting.
-/

namespace CLRS
namespace Chapter08

namespace MutableOutput

/-! ## The mutable output array -/

/--
Scatter the reverse-scan buckets for a list of keys {lit}`ks` into a growing
output {lit}`Array`, appending each key segment via a real {lit}`Array` append.

This is the physical fill loop: {lit}`out` starts empty and each key {lit}`k`
contributes its stable reverse-scan bucket {lit}`ReverseScan.reverseBucket key
xs k` to the right end of {lit}`out`, so the segment for key {lit}`k` occupies a
contiguous block whose left boundary is the cumulative count of the earlier
keys.
-/
def scatter (key : α → Nat) (xs : List α) (ks : List Nat) : Array α :=
  ks.foldl (fun out k => out ++ (ReverseScan.reverseBucket key xs k).toArray) #[]

/--
Reading the scattered output back as a list gives the concatenation of the
per-key reverse-scan buckets.  This is the correctness bridge between the
mutable {lit}`Array` fill and the functional bucket specification.
-/
theorem scatter_toList (key : α → Nat) (xs : List α) (ks : List Nat) :
    (scatter key xs ks).toList = ks.flatMap (ReverseScan.reverseBucket key xs) := by
  unfold scatter
  suffices h : ∀ init : Array α,
      (ks.foldl (fun out k => out ++ (ReverseScan.reverseBucket key xs k).toArray)
          init).toList
        = init.toList ++ ks.flatMap (ReverseScan.reverseBucket key xs) by
    simpa using h #[]
  intro init
  induction ks generalizing init with
  | nil => simp
  | cons k ks ih =>
      rw [List.foldl_cons,
        ih (init ++ (ReverseScan.reverseBucket key xs k).toArray)]
      simp [List.flatMap_cons, List.append_assoc]

/--
Mutable output-array counting sort: fill the output {lit}`Array α` segment by
segment for keys {lit}`0, 1, ..., maxKey`, each segment produced by the stable
reverse scan.  The segment boundaries are the cumulative counts, matching the
prefix-count array of CLRS {lit}`COUNTING-SORT`.
-/
def countingSortArray (maxKey : Nat) (key : α → Nat) (xs : List α) : Array α :=
  scatter key xs (List.range (maxKey + 1))

/--
Array-to-array wrapper of the mutable output refinement: sort the elements of an
{lit}`Array` and return a new {lit}`Array`.  This is the imperative
{lit}`COUNTING-SORT` reading its input from and writing its output to an
{lit}`Array`.
-/
def countingSortInPlace (maxKey : Nat) (key : α → Nat) (a : Array α) : Array α :=
  countingSortArray maxKey key a.toList

/-! ## Refinement of the stable bucket specification -/

/--
**Mutable output-array refinement.**  Reading the mutable output array back as a
list yields exactly the stable bucket specification {lit}`countingSortBy`.  All
correctness properties transfer through this extensional equality.
-/
theorem countingSortArray_toList (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (countingSortArray maxKey key xs).toList = countingSortBy maxKey key xs := by
  unfold countingSortArray
  rw [scatter_toList]
  change ReverseScan.countingSortByReverse maxKey key xs = countingSortBy maxKey key xs
  rw [ReverseScan.countingSortByReverse_eq_countingSortByTable,
    countingSortByTable_eq_countingSortBy]

/-- The array wrapper reads back as the stable bucket specification of its input. -/
theorem countingSortInPlace_toList (maxKey : Nat) (key : α → Nat) (a : Array α) :
    (countingSortInPlace maxKey key a).toList = countingSortBy maxKey key a.toList := by
  unfold countingSortInPlace
  exact countingSortArray_toList maxKey key a.toList

/-- The mutable output array is ordered by key. -/
theorem countingSortArray_ordered (maxKey : Nat) (key : α → Nat) (xs : List α) :
    OrderedBy key (countingSortArray maxKey key xs).toList := by
  rw [countingSortArray_toList]
  exact countingSortBy_ordered maxKey key xs

/--
Per-key stability: for keys bounded by {lit}`maxKey`, filtering the mutable
output array by any key returns exactly the same list as filtering the input.
-/
theorem countingSortArray_bucket_eq
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (k : Nat) :
    bucket key (countingSortArray maxKey key xs).toList k = bucket key xs k := by
  rw [countingSortArray_toList]
  exact countingSortBy_bucket_eq maxKey key xs hxs k

/-- Membership in the mutable output list matches membership in the input. -/
theorem countingSortArray_mem_toList_iff
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (x : α) :
    x ∈ (countingSortArray maxKey key xs).toList ↔ x ∈ xs := by
  rw [countingSortArray_toList]
  exact countingSortBy_mem_iff maxKey key xs hxs x

/-- Membership in the mutable output array matches membership in the input. -/
theorem countingSortArray_mem_iff
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (x : α) :
    x ∈ countingSortArray maxKey key xs ↔ x ∈ xs := by
  rw [← Array.mem_toList_iff]
  exact countingSortArray_mem_toList_iff maxKey key xs hxs x

/-- The mutable output array is a permutation of the input. -/
theorem countingSortArray_perm [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    (countingSortArray maxKey key xs).toList.Perm xs := by
  rw [countingSortArray_toList]
  exact countingSortBy_perm maxKey key xs hxs

/-- Reader-facing correctness theorem for the mutable output-array refinement. -/
theorem countingSortArray_correct [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    OrderedBy key (countingSortArray maxKey key xs).toList ∧
      (∀ k, bucket key (countingSortArray maxKey key xs).toList k = bucket key xs k) ∧
      (∀ x, x ∈ (countingSortArray maxKey key xs).toList ↔ x ∈ xs) ∧
      (countingSortArray maxKey key xs).toList.Perm xs :=
  ⟨countingSortArray_ordered maxKey key xs,
    fun k => countingSortArray_bucket_eq maxKey key xs hxs k,
    fun x => countingSortArray_mem_toList_iff maxKey key xs hxs x,
    countingSortArray_perm maxKey key xs hxs⟩

/-! ## Cumulative-count fill offsets -/

/--
After filling keys {lit}`0..j`, exactly {lit}`cumulativeCount key xs j` output
slots are used.  This is the cumulative-count boundary semantics of CLRS's
prefix-count array {lit}`C`: the fill offset for key {lit}`j + 1` is the number
of elements with key at most {lit}`j`.
-/
theorem scatter_range_size (key : α → Nat) (xs : List α) (j : Nat) :
    (scatter key xs (List.range (j + 1))).size = ReverseScan.cumulativeCount key xs j := by
  rw [← Array.length_toList, scatter_toList]
  unfold ReverseScan.cumulativeCount
  simp [List.length_flatMap, ReverseScan.reverseBucket_eq_bucket]

/--
The full mutable output array has as many slots as the final cumulative count,
i.e. the total number of in-range elements.
-/
theorem countingSortArray_size (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (countingSortArray maxKey key xs).size = ReverseScan.cumulativeCount key xs maxKey := by
  unfold countingSortArray
  exact scatter_range_size key xs maxKey

/--
Under the CLRS precondition that every key lies in {lit}`0..maxKey`, the scatter
performs exactly {lit}`n` writes: the output array has the input length.
-/
theorem countingSortArray_size_of_allKeysLe [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    (countingSortArray maxKey key xs).size = xs.length := by
  rw [← Array.length_toList]
  exact (countingSortArray_perm maxKey key xs hxs).length_eq

/-! ## Linear work bound -/

/--
Per-pass step count of CLRS {lit}`COUNTING-SORT` on an input of length {lit}`n`
with keys in {lit}`0..maxKey`: initialize the {lit}`maxKey + 1` count slots, run
one counting pass over the {lit}`n` inputs, run one prefix-sum pass over the
{lit}`maxKey + 1` counts, and run one scatter pass writing the {lit}`n` inputs
into the output array.
-/
def countingSortArrayCost (maxKey : Nat) (n : Nat) : Nat :=
  (maxKey + 1) + n + (maxKey + 1) + n

/-- The work is the linear expression {lit}`2 * n + 2 * (maxKey + 1)`. -/
theorem countingSortArrayCost_eq (maxKey : Nat) (n : Nat) :
    countingSortArrayCost maxKey n = 2 * n + 2 * (maxKey + 1) := by
  unfold countingSortArrayCost
  omega

/-- The work is bounded by {lit}`2 * (n + maxKey + 1)`, exhibiting linearity in `n + k`. -/
theorem countingSortArrayCost_le (maxKey : Nat) (n : Nat) :
    countingSortArrayCost maxKey n ≤ 2 * (n + (maxKey + 1)) := by
  unfold countingSortArrayCost
  omega

/--
**Linear {lit}`O(n + k)` work bound.**  There is a constant {lit}`c` (here
{lit}`2`) such that the counting-sort work is at most {lit}`c * (n + k + 1)` for
every input length {lit}`n` and maximum key {lit}`k = maxKey`.
-/
theorem countingSortArrayCost_bigO :
    ∃ c : Nat, ∀ maxKey n : Nat,
      countingSortArrayCost maxKey n ≤ c * (n + maxKey + 1) := by
  refine ⟨2, ?_⟩
  intro maxKey n
  unfold countingSortArrayCost
  omega

end MutableOutput

end Chapter08
end CLRS
