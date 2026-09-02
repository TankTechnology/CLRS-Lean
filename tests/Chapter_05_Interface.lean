import CLRSLean.Chapter_05

#check CoinFlip
#check headAt
#check hasRunOfLength
#check longestStreak
#check prob_first_t_heads
#check headAt_eq_of_lt
#check headAt_eq_zero_of_ge
#check streakS
#check card_streakS
#check streakS_all_heads_iff
#check headsSetBijection
#check prob_run_at
#check hasRunOfLength_mono
#check longestStreak_ge_iff_hasRunOfLength
#check fintypeExpect_mono
#check prob_run_at_bound
#check longestStreak_upperBound

#check CLRS.Chapter05.expectedLongestStreak
#check CLRS.Chapter05.OnlineHiring.isAbsoluteBest
#check CLRS.Chapter05.OnlineHiring.isRecordAt
#check CLRS.Chapter05.OnlineHiring.hiringStrategy
#check CLRS.Chapter05.OnlineHiring.hiringStrategy_some_iff
#check CLRS.Chapter05.OnlineHiring.hiringStrategy_none_iff
#check CLRS.Chapter05.OnlineHiring.hiringStrategy_after_observation
#check CLRS.Chapter05.OnlineHiring.hiringStrategy_record
#check CLRS.Chapter05.OnlineHiring.probHireBest

example :
    CLRS.Chapter05.OnlineHiring.hiringStrategy 0
      (Equiv.refl (Fin 0)) = none := by
  native_decide

example :
    CLRS.Chapter05.OnlineHiring.hiringStrategy 3
      (Equiv.refl (Fin 3)) = none := by
  native_decide

example :
    CLRS.Chapter05.OnlineHiring.hiringStrategy 0
      (Equiv.refl (Fin 3)) = some 0 := by
  native_decide

example :
    CLRS.Chapter05.OnlineHiring.hiringStrategy 1
      (Equiv.refl (Fin 3)) = none := by
  native_decide

def onlineHiringLaterPerm : Equiv.Perm (Fin 3) :=
  (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1)

example :
    CLRS.Chapter05.OnlineHiring.hiringStrategy 1
      onlineHiringLaterPerm = some 2 := by
  native_decide
