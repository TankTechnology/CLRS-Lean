import CLRSLean.FourthEdition.Chapter_11.Section_11_5_Perfect_Hashing.Construction

open CLRS.Chapter11 CLRS.Chapter11.PerfectConstruction

private def bad : Hash 2 := fun _ => 0

example : (build [bad, fallback 2]).attempts = 2 := by native_decide
example : (build [bad, fallback 2]).work = 22 := by native_decide
example : (build [fallback 2, bad]).attempts = 1 := by native_decide
example : (build [fallback 2, bad]).work = 11 := by native_decide
example : (build ([] : List (Hash 2))).selected.slots =
    #[some 0, some 1, none, none] := by native_decide
example : (buildTrace (fun _ : Fin 2 => bad)).attempts = 3 := by native_decide
example : (buildTrace (fun _ : Fin 2 => bad)).work = 33 := by native_decide
example : (buildTrace (fun _ : Fin 2 => bad)).selected.success = true := by native_decide
example (i : Fin 2) : perfectSearch (tableOfBuild [bad]) i := tableOfBuild_search _ _
example : (build ([] : List (Hash 0))).work = 0 := by native_decide
example : (build ([] : List (Hash 1))).work = 3 := by native_decide

private def primary : Fin 2 → Fin 2 := fun _ => 0
private def noTrials : (j : Fin 2) → Fin 0 → Hash (bucketCard primary j) :=
  fun _ i => Fin.elim0 i

example : (preparePrimary primary).sizes = #[2, 0] := by native_decide
example : (preparePrimary primary).buckets = #[[0, 1], []] := by native_decide
example : (preparePrimary primary).work = 16 := by native_decide
example : (buildTwoLevel primary noTrials).work = 29 := by native_decide
example : (buildTwoLevel (fun i : Fin 0 => i)
    (fun _ i : Fin 0 => Fin.elim0 i)).work = 0 := by native_decide

#check buildTrace_attempts
#check buildTrace_work_le
#check tableOfBuild_search
#check buildTwoLevel_stores
#check expected_buildTwoLevel_work_le_budget
#check expected_buildTwoLevel_work_lt

example : recoverPayload (buildTwoLevel primary noTrials)
    ⟨0, buildTrace (noTrials 0)⟩ ⟨1, by native_decide⟩ = some 1 := by native_decide
#check buildTwoLevel_recovers_original
#check buildTrace_eq

-- A successful first candidate must not materialize the unused trace suffix.
example : (buildTrace (fun _ : Fin 1000000000 => fallback 2)).attempts = 1 := by native_decide
example : (buildTrace (fun _ : Fin 1000000000 => fallback 2)).work = 11 := by native_decide
