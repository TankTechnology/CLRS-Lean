import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B4_Repair_Swap_Count

/-!
# Dev B5: the iteration to `fifo_optimal`

Development file for the final assembly of the optimality proof (see
`Dev/DESIGN.md`): starting from an arbitrary reduced schedule, repeatedly
repair or exchange at the first disagreement with the FIF schedule, tracking
the reducedness bound and the accumulated slack, until the schedule agrees
with the policy everywhere; the miss count never increases overall.

Main results:

- `exchange_step'`: one exchange at the first disagreement never increases
  misses and extends agreement — with the reducedness hypothesis weakened to
  "from `t` on" (the iteration's schedules are only reduced from a bound on)
- the iteration state machine and `fifo_optimal` (CLRS Theorem 15.5)

This file is part of the `fifo_optimal` iteration; it will be merged into
`S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

/-- Exchanging the first disagreement never increases misses and extends
agreement by one position, assuming the schedule is reduced only from `t`
on. -/
lemma exchange_step' (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ}
    (hdreduced : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hC₀ : C₀.Nonempty)
    (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1)) :
    schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ ≤
      schedMisses d C₀ σ ∧
    agreeWithFIF (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ (t + 1) := by
  let q : Page := d t
  let q' : Page := fifoSchedule σ C₀ t
  have hfd := first_disagree d σ C₀ hC₀ ht hagree hdis
  have hqq' : q ≠ q' := hfd.2.1
  have hft : σ.getD t 0 ∉ schedCache d C₀ σ t := hfd.1
  have hq'res : q' ∈ schedCache d C₀ σ t := hfd.2.2
  have hqin : q ∈ schedCache d C₀ σ t := by
    exact hdreduced t le_rfl hft
  have hfifo : nextUse σ (t + 1) q' = none ∨
      ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' := by
    apply fifo_nextUse_order σ (schedCache d C₀ σ t) t q' q
    · exact fifo_evict_eq_farthest d σ C₀ hagree
    · exact hqin
    · exact hqq'
  constructor
  · exact exchangeSchedule_misses_le d t q q' σ C₀ rfl hqq' hdreduced hft hq'res hfifo
  · intro s hs
    by_cases hs' : s ≤ t
    · rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hs']
      exact hagree s hs'
    · have hst : s = t + 1 := by omega
      subst s
      have hFt : σ.getD t 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ t := by
        rw [← hagree t le_rfl]
        exact hft
      have hE : schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q') := by
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).1 = schedCache d C₀ σ t by
          rw [← schedCache_exchangeScheduleCore]
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).2 = q' by
          exact exchangeSchedule_at_t d t q q' σ C₀]
        rw [if_neg hft]
      have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q') := by
        rw [schedCache_fifoSchedule σ C₀ (t + 1)]
        unfold cacheSeq Policy.step
        rw [← schedCache_fifoSchedule σ C₀ t]
        rw [if_neg hFt]
        congr 2
        · rw [← hagree t le_rfl]
        · change farthestInFuture (schedCache (fifoSchedule σ C₀) C₀ σ t) σ t = q'
          rw [← hagree t le_rfl]
          rw [← fifo_evict_eq_farthest d σ C₀ hagree]
      rw [hE, hF]


end Caching

end CLRS
