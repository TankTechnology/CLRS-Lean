import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.LowerBound
import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.Schedules
import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.Competitive
import CLRSLean.Audit.Axioms
open CLRS.OnlineCaching

example (A : Algorithm (Fin 3) 2) (C : Finset (Fin 3)) (p : Fin 3) (hC : C.card ≤ 2) :
    (A.step C p).card ≤ 2 := A.step_size C p hC
example : Nonempty (Algorithm (Fin 3) 2) := algorithm_nonempty (by decide)
-- An oversized cache no longer produces the old contradiction: only legal-state laws apply.
example : ((flushAlgorithm (Page := Fin 3) (k := 2) (by decide)).step Finset.univ 0).card = 3 := by decide
example : misses (flushAlgorithm (Page := Fin 3) (k := 2) (by decide)) ∅ [0,1,1,2] = 3 := by decide

private def earlier01 : LRUState (Fin 3) 2 := ⟨[0,1], by decide, by decide⟩
private def earlier10 : LRUState (Fin 3) 2 := ⟨[1,0], by decide, by decide⟩
-- Equal resident sets have distinct histories, and therefore different evictions.
example : (lruPolicy (by decide : 0 < 2)).cache earlier01 =
    (lruPolicy (by decide : 0 < 2)).cache earlier10 := by decide
example : ((lruPolicy (by decide : 0 < 2)).step earlier01 2).recency = [2,0] := by decide
example : ((lruPolicy (by decide : 0 < 2)).step earlier10 2).recency = [2,1] := by decide
example : ((lruPolicy (by decide : 0 < 2)).step earlier01 1).recency = [1,0] := by decide

example (b : ℝ) : ∃ xs : List (Fin 3), 0 < xs.length ∧
    (3/2 : ℝ) * (offMisses ∅ (phases 2 xs) : ℝ) + b <
      ((lruPolicy (Page := Fin 3) (by decide : 0 < 2)).misses
        (lruPolicy (by decide : 0 < 2)).initial xs : ℝ) :=
  Policy.no_real_competitive _ (by decide) (3/2) b (by norm_num) (by norm_num)

#assert_axioms algorithm_nonempty
#assert_axioms lruPolicy_misses
#assert_axioms Policy.lru_k_competitive
#assert_axioms Policy.no_real_competitive
#assert_axioms offline_schedule_valid

#assert_axioms Schedule.lru_k_competitive

example (xs : List (Fin 3)) : lruMissesGo 2 [] xs ≤ 2 * offMisses ∅ (phases 2 xs) + 2 :=
  (offline_schedule_valid (by decide : 0 < 2) xs).lru_k_competitive (by decide)
