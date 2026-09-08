import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray
import CLRSLean.FourthEdition.Chapter_08.Section_08_3_Radix_Sort

open CLRS.Chapter08

#check CountingExecution.distribute_get
#check CountingExecution.distribute_toList
#check CountingExecution.execute_result
#check CountingExecution.execute_controllerVisits
#check CountingExecution.execute_indexedWork
#check MutableOutput.countingSortArray_eq_scatter
#check MutableOutput.countingSortArray_execution_cost
#check radixSortByWithIndexedWork_cost_eq
#check radixSortByWithIndexedWork_cost_le

-- Equal keys retain their original payload order through the actual array controller.
example : (MutableOutput.countingSortArray 1 Prod.fst
    [(1, 10), (0, 20), (1, 30)]).toList = [(0, 20), (1, 10), (1, 30)] := by
  native_decide

-- Preserve the specification's unconditional out-of-range behavior.
example : (MutableOutput.countingSortArray 2 Prod.fst
    [(1, 10), (3, 99), (0, 20), (1, 30)]).toList = [(0, 20), (1, 10), (1, 30)] := by
  native_decide

-- Four inputs but only three output pushes; no bounded-key equality is assumed here.
example : (CountingExecution.execute 2 Prod.fst
    [(1, 10), (3, 99), (0, 20), (1, 30)]).controllerVisits = 13 := by
  native_decide

example : (CountingExecution.execute 2 Prod.fst
    [(1, 10), (3, 99), (0, 20), (1, 30)]).indexedWork = 26 := by
  native_decide

-- The original 110-key-test regression now evaluates each of the ten keys once.
example : (CountingExecution.execute 10 id (List.range 10)).inputVisits = 10 := by
  native_decide

example : (CountingExecution.execute 10 id (List.range 10)).controllerVisits = 42 := by
  native_decide

example : (CountingExecution.execute 10 id (List.range 10)).indexedWork = 82 := by
  native_decide

-- Zero available buckets is a valid generic distribution instance.
example : (CountingExecution.distribute id [2, 0, 1] (#[] : Array (List Nat))).buckets = #[] := by
  native_decide

example : (CountingExecution.distribute id [2, 0, 1] (#[] : Array (List Nat))).inputs = 3 := by
  native_decide

example : MutableOutput.countingSortArray 0 id ([] : List Nat) = #[] := by
  native_decide

-- Concrete radix output, including repeated full keys with distinct payloads.
example : radixSortNatBy 10 2 Prod.fst [(21, 0), (12, 1), (21, 2), (11, 3)] =
    [(11, 3), (12, 1), (21, 0), (21, 2)] := by
  native_decide

example : (radixSortByWithCost 9 (baseDigitsLow 10 2 Prod.fst)
    [(21, 0), (12, 1), (21, 2), (11, 3)]).2 = 56 := by
  native_decide

example : (radixSortByWithIndexedWork 9 (baseDigitsLow 10 2 Prod.fst)
    [(21, 0), (12, 1), (21, 2), (11, 3)]).2 = 88 := by
  native_decide

example : radixSortByWithCost 2 [id] [3, 1, 2, 1] = ([1, 1, 2], 13) := by
  native_decide

example : radixSortByWithIndexedWork 9 [] [3, 1, 2] = ([3, 1, 2], 0) := by
  native_decide

-- Existing semantic contracts transfer through the new execution.
example [DecidableEq α] (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    (CountingExecution.execute maxKey key xs).output.toList.Perm xs := by
  rw [CountingExecution.execute_result]
  exact countingSortBy_perm maxKey key xs hxs
