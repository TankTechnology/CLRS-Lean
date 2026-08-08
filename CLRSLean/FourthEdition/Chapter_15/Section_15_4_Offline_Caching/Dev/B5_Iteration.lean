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

end Caching

end CLRS
