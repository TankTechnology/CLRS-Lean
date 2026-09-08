import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort.InsertionExecution
open CLRS.Chapter08.BucketExecution
#check insertionWithCost_value
#check insertionWithCost_perm
#check insertionWithCost_pairwise
#check insertionWithCost_work_le
#check insertionWithCost_work_le_sq

-- Empty and singleton buckets pay their actual execution charges.
example : (insertionWithCost id ([] : List Nat)).work = 0 := by decide
example : (insertionWithCost id [4]).work = 2 := by decide

-- Counters distinguish an early-stopping run from one traversing whole tails.
example : (insertionWithCost id [1, 2, 3]).work = 10 := by decide
example : (insertionWithCost id [3, 2, 1]).work = 12 := by decide

-- Equal ranks retain payloads in their input order under insertion sorting.
example : (insertionWithCost Prod.fst [(1, 10), (0, 20), (1, 30)]).value =
    [(0, 20), (1, 10), (1, 30)] := by decide

example {α : Type} (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).value.Perm xs ∧
      (insertionWithCost rank xs).value.Pairwise (fun x y => rank x ≤ rank y) ∧
      (insertionWithCost rank xs).work ≤ 2 * xs.length ^ 2 :=
  ⟨insertionWithCost_perm rank xs, insertionWithCost_pairwise rank xs,
    insertionWithCost_work_le_sq rank xs⟩
