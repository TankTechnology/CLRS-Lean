import Mathlib
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.CountTables
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.Execution

/-!
# CLRS Section 8.2 - Stable indexed-bucket output-array refinement

The public {lit}`countingSortArray` calls {lit}`CountingExecution.execute`:
one initialization loop, one right-to-left indexed distribution, and one
output loop visiting the stored buckets and pushing their elements. Its array
output equals the existing {lit}`countingSortBy` specification, preserving
orderedness, per-key stability, membership, and permutation contracts.

The older {lit}`scatter` remains a per-key-filter specification helper. It is
not called by the public sorter. Cumulative counts describe output segment
boundaries; the executable does not run the textbook cumulative-counter
decrement program. This is an indexed stable-bucket refinement.

The execution returns counters accumulated in its loops.
{lit}`countingSortArrayCost` is their controller-visit total on bounded keys,
while {lit}`CountingExecution.execute_indexedWork` counts key evaluations,
index checks, reads, cons operations, writes, bucket visits, and output pushes.
These unit-cost ledgers do not model persistent-array copying or machine time.
-/

namespace CLRS
namespace Chapter08

namespace MutableOutput

/-! ## The mutable output array -/

/-- Per-key-filter scatter specification. This helper rescans the input for
every requested key and is not the public linear controller. -/
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

/-- Stable output array from the actual indexed distribution and emission loops. -/
def countingSortArray (maxKey : Nat) (key : α → Nat) (xs : List α) : Array α :=
  (CountingExecution.execute maxKey key xs).output

/--
Array-to-array wrapper of the indexed stable-bucket refinement: read the
input array and return a new sorted output array.
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
  exact CountingExecution.execute_result maxKey key xs

/-- The linear controller is extensionally equal to the older per-key scatter helper. -/
theorem countingSortArray_eq_scatter (maxKey : Nat) (key : α → Nat) (xs : List α) :
    countingSortArray maxKey key xs = scatter key xs (List.range (maxKey + 1)) := by
  apply Array.toList_inj.mp
  rw [countingSortArray_toList, scatter_toList]
  unfold countingSortBy
  apply List.flatMap_congr
  intro k hk
  exact (ReverseScan.reverseBucket_eq_bucket key xs k).symm

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
  rw [countingSortArray_eq_scatter]
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

/-- Controller-visit ledger: initialize each bucket, visit each input once,
visit each stored bucket once, and push each output element once. Bounded
keys make the number of output pushes equal to the input length. -/
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

/-- The actual controller returns the advertised ledger on bounded keys. -/
theorem countingSortArray_execution_cost [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α) (hxs : AllKeysLe key xs maxKey) :
    (CountingExecution.execute maxKey key xs).controllerVisits =
      countingSortArrayCost maxKey xs.length := by
  rw [CountingExecution.execute_controllerVisits maxKey key xs hxs,
    countingSortArrayCost_eq]

/-- Return the output and the controller visits from the same execution. -/
def countingSortArrayWithCost (maxKey : Nat) (key : α → Nat) (xs : List α) : Array α × Nat :=
  let run := CountingExecution.execute maxKey key xs
  (run.output, run.controllerVisits)

theorem countingSortArrayWithCost_result (maxKey : Nat) (key : α → Nat) (xs : List α) :
    (countingSortArrayWithCost maxKey key xs).1 = countingSortArray maxKey key xs := rfl

theorem countingSortArrayWithCost_cost [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α) (hxs : AllKeysLe key xs maxKey) :
    (countingSortArrayWithCost maxKey key xs).2 = countingSortArrayCost maxKey xs.length :=
  countingSortArray_execution_cost maxKey key xs hxs

/-- The expanded indexed-operation ledger remains linear. -/
theorem countingSortArray_indexedWork_le [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α) (hxs : AllKeysLe key xs maxKey) :
    (CountingExecution.execute maxKey key xs).indexedWork ≤
      6 * (xs.length + maxKey + 1) := by
  rw [CountingExecution.execute_indexedWork maxKey key xs hxs]
  omega

end MutableOutput

end Chapter08
end CLRS
