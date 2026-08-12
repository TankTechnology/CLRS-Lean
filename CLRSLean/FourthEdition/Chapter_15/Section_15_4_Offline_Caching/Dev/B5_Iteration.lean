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

set_option maxHeartbeats 400000

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

/-- 若 `d` 与 FIF 一致到 `t0` 但并非处处一致,则存在一个分歧位置
`t ∈ [t0, σ.length)`。 -/
lemma exists_first_disagree_after (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (t0 : ℕ) (ht0 : t0 ≤ σ.length)
    (hagree : agreeWithFIF d C₀ σ t0)
    (hnot : ¬ agreeWithFIF d C₀ σ σ.length) :
    ∃ t, t0 ≤ t ∧ t < σ.length ∧ agreeWithFIF d C₀ σ t ∧
      ¬ agreeWithFIF d C₀ σ (t + 1) := by
  have hmain : ∀ n, t0 ≤ n → n ≤ σ.length → ¬ agreeWithFIF d C₀ σ n →
      ∃ t, t0 ≤ t ∧ t < n ∧ agreeWithFIF d C₀ σ t ∧
        ¬ agreeWithFIF d C₀ σ (t + 1) := by
    intro n
    induction n with
    | zero =>
        intro hnt0 hnol hnotn
        exfalso
        apply hnotn
        intro s hs
        have hs0 : s = 0 := by omega
        subst s
        rfl
    | succ n ih =>
        intro hnt0 hnol hnotn
        by_cases hn : agreeWithFIF d C₀ σ n
        · exact ⟨n, (by
            by_contra h
            have hnlt : n < t0 := by omega
            apply hnotn
            intro s hs
            exact hagree s (by omega)), by omega, hn, hnotn⟩
        · rcases ih (by
            by_contra h
            have hnlt : n < t0 := by omega
            exact hn (by intro s hs; exact hagree s (by omega))) (by omega) hn with
            ⟨t, ht1, ht2, hat, hnat⟩
          exact ⟨t, ht1, by omega, hat, hnat⟩
  rcases hmain σ.length (by omega) le_rfl hnot with ⟨t, ht1, ht2, hat, hnat⟩
  exact ⟨t, ht1, ht2, hat, hnat⟩

/-- 一次 exchange 步骤(情形二:`q'` 会再次被请求):新调度与 FIF 一致到
`t + 1`,miss 不增,且从 `J' + 1` 起 reduced。 -/
lemma exchange_step_full (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {j' : ℕ} (hj' : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = some j') :
    ∃ d' : ℕ → Page,
      agreeWithFIF d' C₀ σ (t + 1) ∧
      schedMisses d' C₀ σ ≤ schedMisses d C₀ σ ∧
      (∀ s, t + 1 + j' < s → σ.getD s 0 ∉ schedCache d' C₀ σ s → d' s ∈ schedCache d' C₀ σ s) := by
  let q : Page := d t
  let q' : Page := fifoSchedule σ C₀ t
  let d' : ℕ → Page := exchangeSchedule d t q q' σ C₀
  have hfd := first_disagree d σ C₀ hC₀ ht hagree hdis
  have hqq' : q ≠ q' := hfd.2.1
  have hft : σ.getD t 0 ∉ schedCache d C₀ σ t := hfd.1
  have hq'res : q' ∈ schedCache d C₀ σ t := hfd.2.2
  have hfifo : nextUse σ (t + 1) q' = none ∨
      ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' := by
    apply fifo_nextUse_order σ (schedCache d C₀ σ t) t q' q
    · exact fifo_evict_eq_farthest d σ C₀ hagree
    · exact hdred t le_rfl hft
    · exact hqq'
  rcases hfifo with hnone | ⟨j, j0', hj, hj0', hjlt⟩
  · exfalso
    rw [hj'] at hnone
    contradiction
  · have hjj0 : j0' = j' := Option.some.inj (hj0'.symm.trans hj')
    have hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact getD_ne_nextUse (k := k) hj' (by omega) (by omega)
    refine ⟨d', ?_, ?_, ?_⟩
    · -- agree 到 t+1
      exact (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    · -- misses 不增
      exact (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).1
    · -- reduced 从 J'+1
      intro s hsJ' hFault
      change exchangeSchedule d t q q' σ C₀ s ∈
        schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
      exact exchangeSchedule_reduced_after d t q q' σ C₀ rfl hqq' hdred hft hq'res
        hj hq'ne (j' := j') hj' hsJ' hFault

/-- 若两个调度的 cache 处处只差永不请求的页面 `P`,则 miss 数相同。 -/
lemma schedMisses_eq_of_cache_diff (d₁ d₂ : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (P : Finset Page)
    (hP : ∀ s, s < σ.length → σ.getD s 0 ∉ P)
    (hdiff₁ : ∀ s, schedCache d₁ C₀ σ s \ schedCache d₂ C₀ σ s ⊆ P)
    (hdiff₂ : ∀ s, schedCache d₂ C₀ σ s \ schedCache d₁ C₀ σ s ⊆ P) :
    schedMisses d₁ C₀ σ = schedMisses d₂ C₀ σ := by
  unfold schedMisses
  apply Finset.sum_congr rfl
  intro s hs
  have hslt : s < σ.length := Finset.mem_range.mp hs
  unfold schedFaultAt
  by_cases hr : σ.getD s 0 ∈ schedCache d₁ C₀ σ s
  · rw [if_pos hr]
    rw [if_pos (by
      by_contra h
      exact hP s hslt (hdiff₁ s (by
        rw [Finset.mem_sdiff]
        exact ⟨hr, h⟩)))]
  · rw [if_neg hr]
    rw [if_neg (by
      intro h₂
      exact hP s hslt (hdiff₂ s (by
        rw [Finset.mem_sdiff]
        exact ⟨h₂, hr⟩)))]


/-- 情形一(`q'` 永不再请求,且 `q` 也不再有请求):交换调度与 `d` 的
cache 处处只差 `q` 与 `q'`,且 fault 处逐出相同。 -/
lemma exchangeSchedule_case_one (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hq'ne : ∀ s, σ.getD s 0 ≠ q')
    (hq_ne : ∀ s, σ.getD s 0 ≠ q)
    (hq_notin : ∀ s, t < s → q ∉ schedCache d C₀ σ s) :
    ∀ s, t < s →
      (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s \ schedCache d C₀ σ s) ⊆ ({q} : Finset Page) ∧
      (schedCache d C₀ σ s \ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) ⊆ ({q'} : Finset Page) ∧
      (σ.getD s 0 ∉ schedCache d C₀ σ s → exchangeSchedule d t q q' σ C₀ s = d s) := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs
      by_cases hs_eq : s = t
      · -- base:t+1
        subst s
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
        have hD : schedCache d C₀ σ (t + 1) =
            insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q) := by
          rw [schedCache]
          rw [if_neg hft]
          rw [← hq]
        have hdsub : schedCache d C₀ σ (t + 1) \
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1) ⊆ ({q'} : Finset Page) := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_singleton]
          have hxE : x ∈ insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q) := by
            rw [← hD]
            exact hx.1
          have hxnotD : x ∉ insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q') := by
            rw [← hE]
            exact hx.2
          rcases Finset.mem_insert.mp hxE with hxr | hxeq
          · exfalso
            exact hxnotD (by rw [hxr]; exact Finset.mem_insert_self _ _)
          · have hxq : x ≠ q := (Finset.mem_erase.mp hxeq).1
            have hxin : x ∈ schedCache d C₀ σ t := (Finset.mem_erase.mp hxeq).2
            have hxnotE : x ∉ (schedCache d C₀ σ t).erase q' := by
              intro hm
              exact hxnotD (Finset.mem_insert.mpr (Or.inr hm))
            have hxq' : x = q' := by
              by_contra hxne
              exact hxnotE (Finset.mem_erase.mpr ⟨hxne, hxin⟩)
            exact hxq'
        constructor
        · -- ex \ d ⊆ {q}
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_singleton]
          have hxE : x ∈ insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q') := by
            rw [← hE]
            exact hx.1
          have hxnotD : x ∉ insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q) := by
            rw [← hD]
            exact hx.2
          rcases Finset.mem_insert.mp hxE with hxr | hxeq'
          · exfalso
            exact hxnotD (by rw [hxr]; exact Finset.mem_insert_self _ _)
          · have hxq' : x ≠ q' := (Finset.mem_erase.mp hxeq').1
            have hxin : x ∈ schedCache d C₀ σ t := (Finset.mem_erase.mp hxeq').2
            have hxnotE : x ∉ (schedCache d C₀ σ t).erase q := by
              intro hm
              exact hxnotD (Finset.mem_insert.mpr (Or.inr hm))
            have hxq : x = q := by
              by_contra hxne
              exact hxnotE (Finset.mem_erase.mpr ⟨hxne, hxin⟩)
            exact hxq
        · constructor
          · exact hdsub
          · -- 逐出相同(t+1 处 fault)
            intro hfault
            unfold exchangeSchedule
            rw [exchangeScheduleCore_second]
            rw [← schedCache_exchangeScheduleCore]
            change exchangeDecision d t q q' σ C₀
              (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1)) (t + 1) = d (t + 1)
            by_cases hdsq' : d (t + 1) = q'
            · unfold exchangeDecision
              rw [if_neg (by omega)]
              rw [if_neg (by omega)]
              rw [if_pos hdsq']
              exact hdsq'.symm
            · have hdsin : d (t + 1) ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1) := by
                have hdsD : d (t + 1) ∈ schedCache d C₀ σ (t + 1) :=
                  hdred (t + 1) (by omega) hfault
                by_cases hdsq : d (t + 1) = q
                · exfalso
                  exact hq_notin (t + 1) (by omega) (hdsq ▸ hdsD)
                · by_contra hnot
                  have hmem : d (t + 1) ∈ schedCache d C₀ σ (t + 1) \
                      schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1) := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hdsD, hnot⟩
                  have hq'eq : d (t + 1) = q' := Finset.mem_singleton.mp (hdsub hmem)
                  exact hdsq' hq'eq
              unfold exchangeDecision
              rw [if_neg (by omega)]
              rw [if_neg (by omega)]
              rw [if_neg hdsq']
              rw [if_neg (by intro h; exact hfault h.2)]
              rw [if_pos hdsin]
      · -- step
        have hsgt : t < s := by omega
        have hih := ih hsgt
        -- 差不变式 1:ex \ d ⊆ {q}(step)
        have hd1 : (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (s + 1) \
            schedCache d C₀ σ (s + 1)) ⊆ ({q} : Finset Page) := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          by_cases hfault : σ.getD s 0 ∉ schedCache d C₀ σ s
          · -- 双 fault
            have hfaultEx : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
              intro h
              have hmem : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s \
                  schedCache d C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨h, hfault⟩
              have hqeq : σ.getD s 0 = q := Finset.mem_singleton.mp (hih.1 hmem)
              exact hq_ne s hqeq
            simp only [schedCache] at hx
            rw [hih.2.2 hfault] at hx
            rw [if_neg hfaultEx, if_neg hfault] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE
            · exfalso
              exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
            · have hxne_ds : x ≠ d s := (Finset.mem_erase.mp hxE).1
              have hxin : x ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
                (Finset.mem_erase.mp hxE).2
              have hxDs : x ∈ schedCache d C₀ σ s → False := by
                intro hxD
                have hxnotD : x ∉ insert (σ.getD s 0) ((schedCache d C₀ σ s).erase (d s)) := hx.2
                exact hxnotD (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxne_ds, hxD⟩)))
              have hxq : x = q := by
                have hmem := hih.1 (by
                  rw [Finset.mem_sdiff]
                  exact ⟨hxin, hxDs⟩)
                exact Finset.mem_singleton.mp hmem
              rw [Finset.mem_singleton]
              exact hxq
          · -- d hit ⟹ ex hit(差页不请求)⟹ 差不变
            have hin : σ.getD s 0 ∈ schedCache d C₀ σ s := by
              by_contra h
              exact hfault h
            have hinEx : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
              by_contra h
              have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \
                  schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hin, h⟩
              have hq'eq : σ.getD s 0 = q' := Finset.mem_singleton.mp (hih.2.1 hmem)
              exact hq'ne s hq'eq
            simp only [schedCache] at hx
            rw [if_pos hinEx, if_pos hin] at hx
            have hxq : x = q := by
              have hmem := hih.1 (Finset.mem_sdiff.mpr ⟨hx.1, hx.2⟩)
              exact Finset.mem_singleton.mp hmem
            rw [Finset.mem_singleton]
            exact hxq
        -- 差不变式 2:d \ ex ⊆ {q'}(step)
        have hd2 : (schedCache d C₀ σ (s + 1) \
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (s + 1)) ⊆ ({q'} : Finset Page) := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          by_cases hfault : σ.getD s 0 ∉ schedCache d C₀ σ s
          · -- 双 fault
            have hfaultEx : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
              intro h
              have hmem : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s \
                  schedCache d C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨h, hfault⟩
              have hqeq : σ.getD s 0 = q := Finset.mem_singleton.mp (hih.1 hmem)
              exact hq_ne s hqeq
            simp only [schedCache] at hx
            rw [hih.2.2 hfault] at hx
            rw [if_neg hfault, if_neg hfaultEx] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE
            · exfalso
              exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
            · have hxne_ds : x ≠ d s := (Finset.mem_erase.mp hxE).1
              have hxin : x ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hxE).2
              have hxEx : x ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s → False := by
                intro hxE2
                have hxnotD : x ∉ insert (σ.getD s 0)
                    ((schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).erase (d s)) := hx.2
                exact hxnotD (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxne_ds, hxE2⟩)))
              have hxq' : x = q' := by
                have hmem := hih.2.1 (by
                  rw [Finset.mem_sdiff]
                  exact ⟨hxin, hxEx⟩)
                exact Finset.mem_singleton.mp hmem
              rw [Finset.mem_singleton]
              exact hxq'
          · -- 双 hit:差不变
            have hin : σ.getD s 0 ∈ schedCache d C₀ σ s := by
              by_contra h
              exact hfault h
            have hinEx : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
              by_contra h
              have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \
                  schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hin, h⟩
              have hq'eq : σ.getD s 0 = q' := Finset.mem_singleton.mp (hih.2.1 hmem)
              exact hq'ne s hq'eq
            simp only [schedCache] at hx
            rw [if_pos hin, if_pos hinEx] at hx
            have hxq' : x = q' := by
              have hmem := hih.2.1 (Finset.mem_sdiff.mpr ⟨hx.1, hx.2⟩)
              exact Finset.mem_singleton.mp hmem
            rw [Finset.mem_singleton]
            exact hxq'
        constructor
        · exact hd1
        · constructor
          · exact hd2
          · -- 逐出相同(step)
            intro hfault
            unfold exchangeSchedule
            rw [exchangeScheduleCore_second]
            rw [← schedCache_exchangeScheduleCore]
            change exchangeDecision d t q q' σ C₀
              (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (s + 1)) (s + 1) = d (s + 1)
            by_cases hdsq' : d (s + 1) = q'
            · unfold exchangeDecision
              rw [if_neg (by omega)]
              rw [if_neg (by omega)]
              rw [if_pos hdsq']
              exact hdsq'.symm
            · have hdsin : d (s + 1) ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (s + 1) := by
                have hdsD : d (s + 1) ∈ schedCache d C₀ σ (s + 1) :=
                  hdred (s + 1) (by omega) hfault
                by_cases hdsq : d (s + 1) = q
                · exfalso
                  exact hq_notin (s + 1) (by omega) (hdsq ▸ hdsD)
                · by_contra hnot
                  have hmem : d (s + 1) ∈ schedCache d C₀ σ (s + 1) \
                      schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (s + 1) := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hdsD, hnot⟩
                  have hq'eq : d (s + 1) = q' := Finset.mem_singleton.mp (hd2 hmem)
                  exact hdsq' hq'eq
              unfold exchangeDecision
              rw [if_neg (by omega)]
              rw [if_neg (by omega)]
              rw [if_neg hdsq']
              rw [if_neg (by intro h; exact hfault h.2)]
              rw [if_pos hdsin]


/-- 情形一、`q` 也永不再请求:交换调度与 `d` 的 miss 数相同。 -/
lemma exchangeSchedule_misses_eq_case_one (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hq'ne : ∀ s, σ.getD s 0 ≠ q')
    (hq_ne : ∀ s, σ.getD s 0 ≠ q)
    (hq_notin : ∀ s, t < s → q ∉ schedCache d C₀ σ s) :
    schedMisses (exchangeSchedule d t q q' σ C₀) C₀ σ = schedMisses d C₀ σ := by
  exact schedMisses_eq_of_cache_diff (exchangeSchedule d t q q' σ C₀) d σ C₀ ({q, q'} : Finset Page)
    (by
      intro s hs h
      rcases Finset.mem_insert.mp h with hqeq | hq'eq
      · exact hq_ne s hqeq
      · have hq'eq' : σ.getD s 0 = q' := Finset.mem_singleton.mp hq'eq
        exact hq'ne s hq'eq')
    (by
      intro s
      by_cases hs : t < s
      · intro x hx
        have hcase := exchangeSchedule_case_one d t q q' σ C₀ hq hdred hft hq'res hq'ne hq_ne hq_notin
        have hmem := (hcase s hs).1 hx
        rw [Finset.mem_singleton] at hmem
        rw [Finset.mem_insert]
        exact Or.inl hmem
      · intro x hx
        exfalso
        have heq : schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s = schedCache d C₀ σ s := by
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ (by omega)
        rw [Finset.mem_sdiff] at hx
        exact hx.2 (heq ▸ hx.1))
    (by
      intro s
      by_cases hs : t < s
      · intro x hx
        have hcase := exchangeSchedule_case_one d t q q' σ C₀ hq hdred hft hq'res hq'ne hq_ne hq_notin
        have hmem := (hcase s hs).2.1 hx
        rw [Finset.mem_singleton] at hmem
        rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_singleton.mpr hmem)
      · intro x hx
        exfalso
        have heq : schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s = schedCache d C₀ σ s := by
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ (by omega)
        rw [Finset.mem_sdiff] at hx
        exact hx.2 (heq ▸ hx.1))


/-- 处处一致 ⟹ miss 数相同。 -/
lemma schedMisses_eq_of_agree (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hagree : agreeWithFIF d C₀ σ σ.length) :
    schedMisses d C₀ σ = schedMisses (fifoSchedule σ C₀) C₀ σ := by
  unfold schedMisses
  apply Finset.sum_congr rfl
  intro s hs
  have hslt : s < σ.length := Finset.mem_range.mp hs
  unfold schedFaultAt
  rw [hagree s (by omega)]

/-- 情形二(`q'` 会再次被请求)的交换步骤,含 slack 更新:
坏事件未发生时(`d` 在 `J'` 处缺页)省一次 miss。 -/
lemma exchange_step_slack (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {j' : ℕ} (hj' : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = some j') :
    ∃ d' slack', agreeWithFIF d' C₀ σ (t + 1) ∧
      schedMisses d' C₀ σ + slack' ≤ schedMisses d C₀ σ + slack := by
  let q : Page := d t
  let q' : Page := fifoSchedule σ C₀ t
  let d' : ℕ → Page := exchangeSchedule d t q q' σ C₀
  by_cases hbad : σ.getD (t + 1 + j') 0 ∈ schedCache d C₀ σ (t + 1 + j')
  · -- 坏事件发生:slack 不变
    refine ⟨d', slack, ?_, ?_⟩
    · simpa [d', q, q'] using (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    · simpa [d', q, q'] using (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).1
  · -- 坏事件未发生:slack + 1
    refine ⟨d', slack + 1, ?_, ?_⟩
    · exact (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    · have hfd := first_disagree d σ C₀ hC₀ ht hagree hdis
      have hqq' : q ≠ q' := hfd.2.1
      have hft : σ.getD t 0 ∉ schedCache d C₀ σ t := hfd.1
      have hq'res : q' ∈ schedCache d C₀ σ t := hfd.2.2
      have hqin : q ∈ schedCache d C₀ σ t := hdred t le_rfl hft
      have hfifo : nextUse σ (t + 1) q' = none ∨
          ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' := by
        apply fifo_nextUse_order σ (schedCache d C₀ σ t) t q' q
        · exact fifo_evict_eq_farthest d σ C₀ hagree
        · exact hqin
        · exact hqq'
      rcases hfifo with hnone | ⟨j, j0', hj, hj0', hjlt⟩
      · exfalso
        rw [hj'] at hnone
        contradiction
      · have hj0eq : j0' = j' := Option.some.inj (hj0'.symm.trans hj')
        have hslack : (nextUse σ (t + 1) q' = none ∧ ∃ j, nextUse σ (t + 1) q = some j) ∨
          ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' ∧
            σ.getD (t + 1 + j') 0 ∉ schedCache d C₀ σ (t + 1 + j') := by
          right
          refine ⟨j, j', hj, hj', ?_, ?_⟩
          · omega
          · simpa [hj0eq] using hbad
        have hle := exchangeSchedule_misses_le_plus_one d t q q' σ C₀ rfl hqq' hdred hft hq'res hslack
        have hle' : schedMisses (exchangeSchedule d t q q' σ C₀) C₀ σ + 1 ≤ schedMisses d C₀ σ := by
          simpa [q, q'] using hle
        unfold d'
        omega


/-- `q'` 永不再请求时,在首个分歧处用策略的选择替换 `e` 的 no-op 逐出,
miss 不增,一致性扩展到 `t + 1`。 -/
lemma repair_q'_never (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    (hq'ne : ∀ s, σ.getD s 0 ≠ q') :
    schedMisses (repairSchedule e t q' t) C₀ σ ≤ schedMisses e C₀ σ ∧
    agreeWithFIF (repairSchedule e t q' t) C₀ σ (t + 1) := by
  let r : ℕ → Page := repairSchedule e t q' t
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t := by
    intro hft
    have hFt : σ.getD t 0 ∈ schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [← hagree t le_rfl]
      exact hft
    have hD : schedCache e C₀ σ (t + 1) = schedCache e C₀ σ t := by
      rw [schedCache]
      rw [if_pos hft]
    have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
        schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [schedCache]
      rw [if_pos hFt]
    exact hdis ((hD.trans (hagree t le_rfl)).trans hF.symm)
  have hq'res : q' ∈ schedCache e C₀ σ t := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    rw [hq']
    exact hfd.2.2
  have hc : ∀ s, s ≤ t → schedCache r C₀ σ s = schedCache e C₀ σ s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih2 =>
        have hst : s ≤ t := by omega
        have hds' : r s = e s := by
          unfold r repairSchedule
          simp [show s ≠ t by omega]
        rw [schedCache, schedCache]
        rw [ih2 hst]
        rw [hds']
  have hdiff : ∀ s, (schedCache r C₀ σ s \ schedCache e C₀ σ s ⊆ ({q'} : Finset Page)) ∧
      (schedCache e C₀ σ s \ schedCache r C₀ σ s ⊆ ({q'} : Finset Page)) := by
    intro s
    induction s with
    | zero =>
        constructor
        · intro x hx
          exfalso
          simp [r, schedCache, Finset.mem_sdiff] at hx
        · intro x hx
          exfalso
          simp [r, schedCache, Finset.mem_sdiff] at hx
    | succ s ih =>
        by_cases hs_eq : s = t
        · -- base:t+1
          subst s
          have hE : schedCache r C₀ σ (t + 1) =
              insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
            rw [schedCache]
            rw [hc t le_rfl]
            rw [if_neg hft]
            unfold r repairSchedule
            simp
          have hD : schedCache e C₀ σ (t + 1) =
              insert (σ.getD t 0) (schedCache e C₀ σ t) := by
            rw [schedCache]
            rw [if_neg hft]
            rw [Finset.erase_eq_of_notMem hnoop]
          constructor
          · -- r \ e ⊆ {q'}
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            have hxE : x ∈ insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
              rw [← hE]
              exact hx.1
            have hxnotD : x ∉ insert (σ.getD t 0) (schedCache e C₀ σ t) := by
              rw [← hD]
              exact hx.2
            rcases Finset.mem_insert.mp hxE with hxr | hxeq
            · exfalso
              exact hxnotD (by rw [hxr]; exact Finset.mem_insert_self _ _)
            · have hxin : x ∈ schedCache e C₀ σ t := (Finset.mem_erase.mp hxeq).2
              have hxnotE : x ∉ schedCache e C₀ σ t := by
                intro hm
                exact hxnotD (Finset.mem_insert.mpr (Or.inr hm))
              exfalso
              exact hxnotE hxin
          · -- e \ r ⊆ {q'}
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            have hxE : x ∈ insert (σ.getD t 0) (schedCache e C₀ σ t) := by
              rw [← hD]
              exact hx.1
            have hxnotD : x ∉ insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
              rw [← hE]
              exact hx.2
            rcases Finset.mem_insert.mp hxE with hxr | hxin
            · exfalso
              exact hxnotD (by rw [hxr]; exact Finset.mem_insert_self _ _)
            · have hxnotE : x ∉ (schedCache e C₀ σ t).erase q' := by
                intro hm
                exact hxnotD (Finset.mem_insert.mpr (Or.inr hm))
              have hxq' : x = q' := by
                by_contra hxne
                exact hxnotE (Finset.mem_erase.mpr ⟨hxne, hxin⟩)
              exact hxq'
        · -- step
          have hsne_t : s ≠ t := hs_eq
          have hds : r s = e s := by
            unfold r repairSchedule
            simp [hsne_t]
          have hmem_eq : ∀ x, x ≠ q' → (x ∈ schedCache r C₀ σ s ↔ x ∈ schedCache e C₀ σ s) := by
            intro x hxq'
            constructor
            · intro hxr
              by_contra hxe
              have hmem : x ∈ schedCache r C₀ σ s \ schedCache e C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxr, hxe⟩
              have hxq : x = q' := Finset.mem_singleton.mp (ih.1 hmem)
              exact hxq' hxq
            · intro hxe
              by_contra hxr
              have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxe, hxr⟩
              have hxq : x = q' := Finset.mem_singleton.mp (ih.2 hmem)
              exact hxq' hxq
          have hfault_eq : (σ.getD s 0 ∈ schedCache r C₀ σ s) ↔
              (σ.getD s 0 ∈ schedCache e C₀ σ s) := by
            exact hmem_eq (σ.getD s 0) (hq'ne s)
          constructor
          · -- r \ e ⊆ {q'} 保持
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            by_cases hfault : σ.getD s 0 ∉ schedCache e C₀ σ s
            · -- 双 fault
              have hfaultR : σ.getD s 0 ∉ schedCache r C₀ σ s := by
                intro h
                exact hfault (hfault_eq.mp h)
              rw [schedCache, schedCache] at hx
              rw [hds] at hx
              rw [if_neg hfaultR, if_neg hfault] at hx
              rcases Finset.mem_insert.mp hx.1 with hxr | hxE
              · exfalso
                exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
              · have hxne_ds : x ≠ e s := (Finset.mem_erase.mp hxE).1
                have hxin : x ∈ schedCache r C₀ σ s := (Finset.mem_erase.mp hxE).2
                have hxEe : x ∈ schedCache e C₀ σ s → False := by
                  intro hxEe
                  have hxnotD : x ∉ insert (σ.getD s 0) ((schedCache e C₀ σ s).erase (e s)) := hx.2
                  exact hxnotD (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxne_ds, hxEe⟩)))
                have hxq : x = q' := by
                  have hmem := ih.1 (by
                    rw [Finset.mem_sdiff]
                    exact ⟨hxin, hxEe⟩)
                  exact Finset.mem_singleton.mp hmem
                exact hxq
            · -- 双 hit(差页 `q'` 不请求 ⟹ 同 hit)
              have hin : σ.getD s 0 ∈ schedCache e C₀ σ s := by
                by_contra h
                exact hfault h
              have hinR : σ.getD s 0 ∈ schedCache r C₀ σ s := hfault_eq.mpr hin
              rw [schedCache, schedCache] at hx
              rw [if_pos hinR, if_pos hin] at hx
              have hxq : x = q' := by
                have hmem := ih.1 (Finset.mem_sdiff.mpr hx)
                exact Finset.mem_singleton.mp hmem
              exact hxq
          · -- e \ r ⊆ {q'} 保持
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            by_cases hfault : σ.getD s 0 ∉ schedCache e C₀ σ s
            · -- 双 fault
              have hfaultR : σ.getD s 0 ∉ schedCache r C₀ σ s := by
                intro h
                exact hfault (hfault_eq.mp h)
              rw [schedCache, schedCache] at hx
              rw [hds] at hx
              rw [if_neg hfault, if_neg hfaultR] at hx
              rcases Finset.mem_insert.mp hx.1 with hxr | hxE
              · exfalso
                exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
              · have hxne_ds : x ≠ e s := (Finset.mem_erase.mp hxE).1
                have hxin : x ∈ schedCache e C₀ σ s := (Finset.mem_erase.mp hxE).2
                have hxEr : x ∈ schedCache r C₀ σ s → False := by
                  intro hxEr
                  have hxnotD : x ∉ insert (σ.getD s 0) ((schedCache r C₀ σ s).erase (e s)) := hx.2
                  exact hxnotD (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxne_ds, hxEr⟩)))
                have hxq : x = q' := by
                  have hmem := ih.2 (by
                    rw [Finset.mem_sdiff]
                    exact ⟨hxin, hxEr⟩)
                  exact Finset.mem_singleton.mp hmem
                exact hxq
            · -- 双 hit
              have hin : σ.getD s 0 ∈ schedCache e C₀ σ s := by
                by_contra h
                exact hfault h
              have hinR : σ.getD s 0 ∈ schedCache r C₀ σ s := hfault_eq.mpr hin
              rw [schedCache, schedCache] at hx
              rw [if_pos hin, if_pos hinR] at hx
              have hxq : x = q' := by
                have hmem := ih.2 (Finset.mem_sdiff.mpr hx)
                exact Finset.mem_singleton.mp hmem
              exact hxq
  constructor
  · -- misses:r ≤ e(差页 `q'` 不请求)
    have hmiss : schedMisses r C₀ σ = schedMisses e C₀ σ := by
      exact schedMisses_eq_of_cache_diff r e σ C₀ ({q'} : Finset Page)
        (by
          intro s hs h
          exact hq'ne s (Finset.mem_singleton.mp h))
        (fun s => (hdiff s).1)
        (fun s => (hdiff s).2)
    rw [hmiss]
  · -- agree 到 t+1
    intro s hs
    by_cases hs' : s ≤ t
    · -- s ≤ t:通过 `hc`(repair 与 e 相同)和 `hagree`
      rw [hc s hs']
      exact hagree s hs'
    · -- s = t+1
      have hst : s = t + 1 := by omega
      subst s
      have hE : schedCache r C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
        rw [schedCache]
        rw [hc t le_rfl]
        rw [if_neg hft]
        unfold r repairSchedule
        simp
      have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
        rw [schedCache_fifoSchedule σ C₀ (t + 1)]
        unfold cacheSeq Policy.step
        rw [← schedCache_fifoSchedule σ C₀ t]
        rw [if_neg (by rw [← hagree t le_rfl]; exact hft)]
        congr 2
        · rw [hagree t le_rfl]
        · change farthestInFuture (schedCache (fifoSchedule σ C₀) C₀ σ t) σ t = q'
          rw [← hagree t le_rfl]
          rw [← fifo_evict_eq_farthest e σ C₀ hagree]
          rw [hq']
      rw [hE, hF]


/-- 窗口内(`t ≤ s < J'`)的交换调度在 `s` 处 fault 时,逐出要么是 resident
(分支 2-6),要么等于窗口页 `q'`(分支 1)。 -/
lemma exchangeSchedule_window_evict (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q)
    (hqq' : q ≠ q')
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    (hjj' : j < j')
    {s : ℕ} (hs1 : t < s) (hs2 : s < t + 1 + j')
    (hFault : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) :
    exchangeSchedule d t q q' σ C₀ s = q' ∨
    exchangeSchedule d t q q' σ C₀ s ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  by_cases hdsq' : d s = q'
  · -- 分支 1:逐出 `q'`
    left
    unfold exchangeSchedule
    rw [exchangeScheduleCore_second]
    rw [← schedCache_exchangeScheduleCore]
    change exchangeDecision d t q q' σ C₀
      (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s = q'
    unfold exchangeDecision
    rw [if_neg (by omega)]
    rw [if_neg (by omega)]
    rw [if_pos hdsq']
  · -- 分支 5/6:逐出 resident
    right
    change (exchangeScheduleCore d t q q' σ C₀ s).2 ∈
      schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
    rw [exchangeScheduleCore_second]
    rw [← schedCache_exchangeScheduleCore]
    change exchangeDecision d t q q' σ C₀
      (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s ∈
      schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
    unfold exchangeDecision
    rw [if_neg (by omega)]
    rw [if_neg (by omega)]
    rw [if_neg hdsq']
    by_cases hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
        σ.getD s 0 ∈ schedCache d C₀ σ s
    · -- 分支 4:多集元素 ∈ C' \ E ⊆ C'
      rw [if_pos hb4]
      let M : Finset Page := schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s \
        schedCache d C₀ σ s
      by_cases hf : (M.filter (fun x => x ≠ q')).Nonempty
      · rw [dif_pos hf]
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Classical.choose_spec hf)).1).1
      · rw [dif_neg hf]
        by_cases hm : M.Nonempty
        · rw [dif_pos hm]
          exact (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
        · rw [dif_neg hm]
          exfalso
          -- M 空 ⟹ C' ⊆ E;card 论证 ⟹ C' = E ⟹ 请求 ∈ C'(矛盾 — hFault)
          have hsub : schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s ⊆
              schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤
              (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).card := by
            rw [schedCache_exchangeScheduleCore]
            exact exchangeScheduleCore_card d t q q' σ C₀ hdred (by omega)
          have hEq : schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s =
              schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          exact hFault (hEq.symm ▸ hb4.2)
    · -- 分支 5:d s ∈ C'
      rw [if_neg hb4]
      have hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
        intro k hk1 hk2
        exact getD_ne_nextUse (k := k) hj' (by omega) (by omega)
      have hdFault : σ.getD s 0 ∉ schedCache d C₀ σ s := by
        intro hdHit
        by_cases hqeq' : σ.getD s 0 = q'
        · exact getD_ne_nextUse (k := s) hj' (by omega) (by omega) hqeq'
        · by_cases hqeq : σ.getD s 0 = q
          · have hqex : q ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
              exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hdred hft hq'res hj hq'ne
                s (by omega) (hqeq ▸ hdHit)
            exact hFault (hqeq ▸ hqex)
          · have hxex := exchangeSchedule_invariant d t q q' σ C₀ hq hdred s (by omega)
              (σ.getD s 0)
              (by
                intro h
                rcases Finset.mem_insert.mp h with hqeq1 | hqeq'1
                · exact hqeq hqeq1
                · exact hqeq' (Finset.mem_singleton.mp hqeq'1))
              hdHit
            exact hFault hxex
      have hdsin : d s ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
        have hdsD : d s ∈ schedCache d C₀ σ s := hdred s (by omega) hdFault
        by_cases hdsq : d s = q
        · -- d s = q:q ∈ cache d s ⟹ q ∈ ex cache(`exchangeSchedule_q_mem`)
          rw [hdsq]
          exact exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hdred hft hq'res hj hq'ne
            s (by omega) (hdsq ▸ hdsD)
        · -- d s ∉ {q, q'}:`exchangeSchedule_invariant`
          exact exchangeSchedule_invariant d t q q' σ C₀ hq hdred s (by omega) (d s)
            (by
              intro h
              rcases Finset.mem_insert.mp h with hqeq | hq'eq
              · exact hdsq hqeq
              · exact hdsq' (Finset.mem_singleton.mp hq'eq))
            hdsD
      rw [if_pos hdsin]
      exact hdsin


/-- 若 `q'` 在 `t` 处被 `d` 真逐出(且 `t` 处 `d` 缺页),则到其首次请求
`J'` 为止 `q'` 不在 `d` 的 cache 中(坏事件未发生)。 -/
lemma evicted_page_absent_until_request (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (t : ℕ) (q' : Page)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hevict : d t = q')
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j') :
    q' ∉ schedCache d C₀ σ (t + 1 + j') := by
  have hmain : ∀ s, t + 1 ≤ s → s ≤ t + 1 + j' → q' ∉ schedCache d C₀ σ s := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hst : s = t
        · -- base:s+1 = t+1
          subst s
          rw [schedCache]
          rw [if_neg hft]
          rw [hevict]
          intro hm
          rcases Finset.mem_insert.mp hm with hq'r | hq'E
          · exact hft (hq'r.symm ▸ hq'res)
          · exact (Finset.mem_erase.mp hq'E).1 rfl
        · -- step:q' 在 s 处不在(ih),且 s 处请求 ≠ q'
          have hs1' : t + 1 ≤ s := by omega
          have hs2' : s ≤ t + 1 + j' := by omega
          have hq'not : q' ∉ schedCache d C₀ σ s := ih hs1' hs2'
          have hneq : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
          rw [schedCache]
          by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
          · rw [if_pos hr]
            exact hq'not
          · rw [if_neg hr]
            intro hm
            rcases Finset.mem_insert.mp hm with hq'r | hq'E
            · exact hneq hq'r.symm
            · exact hq'not (Finset.mem_erase.mp hq'E).2
  exact hmain (t + 1 + j') (by omega) le_rfl


/-- 窗口内分支 1 不会出现两次:若源 `d` 在 `s₁` 和 `s₂`(都在窗口内、`s₁ < s₂`)
都逐出 `q'`(两处都缺页),则矛盾:源从 `t` 起 reduced ⟹ `s₂` 处 `q' ∈ cache`;
而 `s₁` 处真逐出后 `q'` 无法重新进入(首次请求在 `J'`)。
在迭代中这保证 case B 处的分支 1 是窗口内第一次 ⟹ 真逐出 ⟹ 坏事件未发生。 -/
lemma window_branch1_once (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    {s₁ : ℕ} (hs1 : t < s₁) (hs1' : s₁ < t + 1 + j')
    {s₂ : ℕ} (hs2 : t < s₂) (hs2lt : s₁ < s₂) (hs2' : s₂ < t + 1 + j')
    (hbranch₁ : d s₁ = q') (hbranch₂ : d s₂ = q')
    (hFault₁ : σ.getD s₁ 0 ∉ schedCache d C₀ σ s₁)
    (hFault₂ : σ.getD s₂ 0 ∉ schedCache d C₀ σ s₂) :
    False := by
  have hq'in₂ : q' ∈ schedCache d C₀ σ s₂ := by
    exact hbranch₂ ▸ hdred s₂ (by omega) hFault₂
  -- q' ∈ cache s₂ 且 (s₁, s₂] 内无 q' 请求 ⟹ q' ∈ cache s₁(从未被真逐出)
  have hq'in₁ : q' ∈ schedCache d C₀ σ s₁ := by
    by_contra hnot
    have hqback : ∀ k, k ≤ s₂ → s₁ ≤ k → q' ∈ schedCache d C₀ σ k → q' ∈ schedCache d C₀ σ s₁ := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk2 hk1 hqk
          by_cases hk_eq : k = s₁
          · simpa [hk_eq] using hqk
          · have hk'1 : s₁ ≤ k - 1 := by omega
            have hk'2 : k - 1 ≤ s₂ := by omega
            have hqk' : q' ∈ schedCache d C₀ σ (k - 1) := by
              have hkeq : k = (k - 1) + 1 := by omega
              have hqk'' : q' ∈ schedCache d C₀ σ ((k - 1) + 1) := hkeq ▸ hqk
              rw [schedCache] at hqk''
              by_cases hr : σ.getD (k - 1) 0 ∈ schedCache d C₀ σ (k - 1)
              · rw [if_pos hr] at hqk''
                exact hqk''
              · rw [if_neg hr] at hqk''
                rcases Finset.mem_insert.mp hqk'' with hq'r | hq'E
                · exfalso
                  exact getD_ne_nextUse (k := k - 1) hj' (by omega) (by omega) hq'r.symm
                · exact (Finset.mem_erase.mp hq'E).2
            exact ih (k - 1) (by omega) hk'2 hk'1 hqk'
    exact hnot (hqback s₂ le_rfl (by omega) hq'in₂)
  -- s₁ 处真逐出(源 reduced ⟹ q' ∈ cache s₁、d s₁ = q')⟹ q' ∉ cache s₁+1
  have hq'out : q' ∉ schedCache d C₀ σ (s₁ + 1) := by
    rw [schedCache]
    rw [if_neg hFault₁]
    rw [hbranch₁]
    intro hm
    rcases Finset.mem_insert.mp hm with hq'r | hq'E
    · exfalso
      exact getD_ne_nextUse (k := s₁) hj' (by omega) (by omega) hq'r.symm
    · exact (Finset.mem_erase.mp hq'E).1 rfl
  -- q' ∉ cache s₁+1 且 (s₁+1, s₂] 内无 q' 请求 ⟹ q' ∉ cache s₂ — 矛盾
  have hq'out₂ : q' ∉ schedCache d C₀ σ s₂ := by
    have hnoenter : ∀ k, s₁ + 1 ≤ k → k ≤ s₂ → q' ∉ schedCache d C₀ σ k := by
      intro k
      induction k with
      | zero => omega
      | succ k ih =>
          intro hk1 hk2
          by_cases hk1' : s₁ + 1 ≤ k
          · have hqnot : q' ∉ schedCache d C₀ σ k := ih hk1' (by omega)
            rw [schedCache]
            by_cases hr : σ.getD k 0 ∈ schedCache d C₀ σ k
            · rw [if_pos hr]
              exact hqnot
            · rw [if_neg hr]
              intro hm
              rcases Finset.mem_insert.mp hm with hq'r | hq'E
              · exfalso
                exact getD_ne_nextUse (k := k) hj' (by omega) (by omega) hq'r.symm
              · exact hqnot (Finset.mem_erase.mp hq'E).2
          · have hk1eq : k + 1 = s₁ + 1 := by omega
            simpa [hk1eq] using hq'out
    exact hnoenter s₂ (by omega) le_rfl
  exact hq'out₂ hq'in₂

end Caching

end CLRS
