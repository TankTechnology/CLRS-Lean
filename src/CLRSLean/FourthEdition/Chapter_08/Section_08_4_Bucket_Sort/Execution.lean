import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.Execution
import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort.InsertionExecution

/-!
# Single-distribution bucket sorting with insertion work

The shared indexed distributor traverses the input once, keeping each bucket
in input order. This controller visits each stored bucket, executes counted
insertion sort, and pushes its output elements. Initialization, input key/index
operations, bucket visits, output writes, and insertion work all contribute to
the returned counter. Indexed operations use the declared unit-cost model;
allocation internals, persistent-array copying, array/list view conversion, and
key-function internals are excluded.
-/

namespace CLRS.Chapter08.BucketExecution

structure Emission (α : Type*) where
  output : Array α
  bucketVisits : Nat
  outputWrites : Nat
  sortingWork : Nat

def sortEmit (rank : α → Nat) : List (List α) → Array α → Emission α
  | [], out => ⟨out, 0, 0, 0⟩
  | b :: bs, out =>
      let sorted := insertionWithCost rank b
      let pushed := CountingExecution.pushList sorted.value out
      let rest := sortEmit rank bs pushed.value
      ⟨rest.output, rest.bucketVisits + 1, pushed.writes + rest.outputWrites,
        sorted.work + rest.sortingWork⟩

theorem sortEmit_value (rank : α → Nat) (bs : List (List α)) (out : Array α) :
    (sortEmit rank bs out).output.toList =
      out.toList ++ bs.flatMap (fun b => (insertionWithCost rank b).value) := by
  induction bs generalizing out with
  | nil => simp [sortEmit]
  | cons b bs ih => simp [sortEmit, ih, List.append_assoc]

theorem sortEmit_visits (rank : α → Nat) (bs : List (List α)) (out : Array α) :
    (sortEmit rank bs out).bucketVisits = bs.length := by
  induction bs generalizing out with
  | nil => rfl
  | cons b bs ih => simp [sortEmit, ih]

theorem sortEmit_writes (rank : α → Nat) (bs : List (List α)) (out : Array α) :
    (sortEmit rank bs out).outputWrites = bs.flatten.length := by
  induction bs generalizing out with
  | nil => rfl
  | cons b bs ih => simp [sortEmit, ih, insertionWithCost_length]

theorem sortEmit_work_le (rank : α → Nat) (bs : List (List α)) (out : Array α) :
    (sortEmit rank bs out).sortingWork ≤ 2 * (bs.map (fun b => b.length ^ 2)).sum := by
  induction bs generalizing out with
  | nil => simp [sortEmit]
  | cons b bs ih =>
      simp only [sortEmit, List.map_cons, List.sum_cons]
      have hrest := ih (CountingExecution.pushList (insertionWithCost rank b).value out).value
      have hb := insertionWithCost_work_le_sq rank b
      omega

structure Result (α : Type*) where
  output : Array α
  work : Nat

/-- The public bucket execution calls the distributor and both counted output loops. -/
def execute (bucketCount : Nat) (bucketOf rank : α → Nat) (xs : List α) : Result α :=
  let initial := CountingExecution.initializeBuckets (α := α) bucketCount
  let distributed := CountingExecution.distribute bucketOf xs initial.1
  let emitted := sortEmit rank distributed.buckets.toList #[]
  ⟨emitted.output, initial.2 + 2 * distributed.inputs + 3 * distributed.updates +
    emitted.bucketVisits + emitted.outputWrites + emitted.sortingWork⟩

theorem execute_value (bucketCount : Nat) (bucketOf rank : α → Nat) (xs : List α) :
    (execute bucketCount bucketOf rank xs).output.toList =
      (List.range bucketCount).flatMap
        (fun k => (insertionWithCost rank (bucket bucketOf xs k)).value) := by
  simp [execute, sortEmit_value, CountingExecution.distribute_toList, List.flatMap_map]

/-- The bound includes the number of buckets even when the input is empty. -/
theorem execute_work_le (bucketCount : Nat) (bucketOf rank : α → Nat) (xs : List α) :
    (execute bucketCount bucketOf rank xs).work ≤
      2 * bucketCount + 5 * xs.length +
        ((List.range bucketCount).map (bucket bucketOf xs)).flatten.length +
        2 * ((List.range bucketCount).map
          (fun k => (bucket bucketOf xs k).length ^ 2)).sum := by
  let bs := (List.range bucketCount).map (bucket bucketOf xs)
  have hs := sortEmit_work_le rank bs #[]
  have hu := CountingExecution.distribute_updates_le bucketOf xs
    (Array.replicate bucketCount [])
  simp only [execute, CountingExecution.initializeBuckets_array,
    CountingExecution.initializeBuckets_visits, CountingExecution.distribute_inputs,
    CountingExecution.distribute_toList, sortEmit_visits, sortEmit_writes, List.length_map,
    List.length_range]
  simpa only [bs, List.map_map, Function.comp_def] using (by omega :
    bucketCount + 2 * xs.length +
      3 * (CountingExecution.distribute bucketOf xs (Array.replicate bucketCount [])).updates +
      bucketCount + bs.flatten.length + (sortEmit rank bs #[]).sortingWork ≤
      2 * bucketCount + 5 * xs.length + bs.flatten.length +
      2 * (bs.map (fun b => b.length ^ 2)).sum)

end CLRS.Chapter08.BucketExecution
