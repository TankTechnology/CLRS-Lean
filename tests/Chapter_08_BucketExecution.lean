import CLRSLean.FourthEdition.Chapter_08
open CLRS.Chapter08
#check bucketSortByRankWithCost_work_le
#check expectedBucketExecutionWork_isBigO

-- Actual public distribution, sorting, and emission.
example : bucketSortByRank 3 (fun x => x / 10) id [21, 12, 11, 22] = [11, 12, 21, 22] := by
  decide

-- Equal-rank payloads retain their input order through distribution and sorting.
example : bucketSortByRank 1 (fun _ : Nat × Nat => 0) Prod.fst
    [(1, 9), (1, 3), (1, 7)] = [(1, 9), (1, 3), (1, 7)] := by decide

-- Bucket initialization/traversal has a cost even without input elements.
example : bucketSortByRankWithCost 3 id id ([] : List Nat) = ([], 6) := by decide
example : bucketSortByRankWithCost 0 id id [1, 2] = ([], 4) := by decide

-- Out-of-range values retain the previous specified omission behavior.
example : bucketSortByRank 2 id id [1, 7, 0, 1] = [0, 1, 1] := by decide

example (a : Fin 4 → Fin 4) (rank : Fin 4 → Nat) :
    ((bucketSortByRankWithCost 4 (fun i => (a i : Nat)) rank (List.finRange 4)).2 : ℝ) ≤
      24 + 2 * textbookBucketSortCost 4 a := by
  calc
    _ ≤ 6 * (4 : ℝ) + 2 * textbookBucketSortCost 4 a :=
      bucketExecutionWork_le_budget a rank
    _ = 24 + 2 * textbookBucketSortCost 4 a := by ring

-- Expected runtime is a bound on the returned counter, for any rank assignment.
example (rank : (Fin 4 → Fin 4) → Fin 4 → Nat) :
    CLRS.Probability.fintypeExpect (fun a : Fin 4 → Fin 4 =>
      ((bucketSortByRankWithCost 4 (fun i => (a i : Nat)) (rank a)
        (List.finRange 4)).2 : ℝ)) ≤ 48 := by
  calc
    _ ≤ 12 * (4 : ℝ) := expectedBucketExecutionWork_le 4 (by norm_num) rank
    _ = 48 := by norm_num
