import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B6_Strong_Repair

/-!
# Dev B7: the iteration assembly (repair diff invariants)

Development file for the iteration assembly of the `fifo_optimal` proof (see
`Dev/DESIGN.md`): the reverse-diff invariants of a B2 repair.  At a B2
position `t` (inside the window of the last case-A exchange), with
`q = e t` resident and `q'' = fifoSchedule σ C₀ t` both alive (`j < j''`),
the repair `r = repairSchedule e t q'' (t + 1 + j'')` evicts `q''` at `t`
and at `J'' = t + 1 + j''`, keeps `q` (the keep-swap `q ∈ Ŝ_J` at the good
event `J = t + 1 + j`, proved later by `b2_hswap`), and otherwise follows
`e`.  The reverse diff `E − Ŝ` is then confined to the repair pages:

- up to `J`: `⊆ {q, q''}` (`repair_cache_diff_le`, B6);
- on `(J, J'']`: `⊆ {q''}` — the base at `J + 1` uses the keep-swap and
  `repair_cache_diff_le` at `J`, the step only `r s = e s` and
  `σ[s] ≠ q''`;
- after `J''`: `E ⊆ Ŝ` — at `J''` both sides gain `q''`, and `r s = e s`
  afterwards preserves the containment.

The forward diff `Ŝ − E` is *not* confined after `J` (it picks up `e J`,
the page `e` evicts at the good event — the drift that can only grow
forward), so the reverse-diff chain of `iterate_main` (`E − D ⊆ Q''`)
uses only these one-directional statements.

Main results:

- `repair_reverse_diff_window`: on `(J, J'']`, `E − Ŝ ⊆ {q''}`
- `repair_reverse_diff_after`: after `J''`, `E − Ŝ = ∅` (i.e. `E ⊆ Ŝ`)
- `repair_diff_all`: the assembly — `E − Ŝ ⊆ {q, q''}` everywhere,
  `⊆ {q''}` on `(J, J'']`, and `∅` after `J''`
- `reverse_diff_chain`: the chain invariant `E − D ⊆ Q` of `iterate_main`
  extends through a repair by only `q''` — `E − Ŝ ⊆ insert q'' Q`
- `reverse_diff_chain_qp_dead` / `reverse_diff_chain_q_dead`: same for the
  dead-page repairs — `q''` dead (alive-`q` case, `repair_cache_diff_le` +
  `repair_cache_diff_after`) and both dead (`repair_cache_diff`), for the
  `repairSchedule d t q'' t` form
- `b2_ehit`: the local e-hit step — at a B2 disagreement `t` (d faults,
  chain at `t`), `σ[t] ∈ E_t ⟹ σ[t] ∈ Q`
- `b2_ehit_ne`: the contradiction side — dead or not-yet-requested past
  repair pages exclude `σ[t]` from `Q.image Prod.snd`
- `b2_no_evict_q`: the keep-swap core — at faults `s ∈ (t, J]` of the
  exchange schedule, `d s = e s` (off the past repair/nop positions `P`)
  and `e s ≠ q` (`exchange_no_evict_q`, with the e-hit at `t` derived via
  `b2_ehit` + `b2_ehit_ne`)
- `b2_hswap`: the swap form at the good event — `Ŝ_J = insert q (E_J −
  q'')`, the instantiation of `repair_keep_swap` (B6) with the window
  hypotheses
- `repair_keep_swap_cur`: the swap form for the repair of the **current**
  schedule (exchange + past repairs) — `Ŝ_J = insert q (D_J − q'')`, the
  bridge: `hd_eq`/`hnot`/`ht₂notP` (off `P`, `d = e`), `hqinE` (the branch
  analysis), `hnotE` (e-faults on the window), the e-hit at `t₂` via
  `b2_ehit` + `b2_ehit_ne`
- `repair_keep_swap_cur_qp_dead`: the same for the `q''`-dead case — the
  dead-page repair `repairSchedule d t₂ q'' t₂` (nop = `t₂`) still has the
  swap form at `J` (the good event), giving `reverse_diff_chain_qp_dead`'s
  `hkept` for the B2-q''-dead step
- `exchange_evict_mem_or_q'`: the branch analysis — at an exchange fault
  in the window, the eviction is `q₀'` or resident (`e s ∈ E_s ∪ {q₀'}`);
  the mechanism behind `hqinE` (at B2 the `q₀'` branch is B1) and "the
  exchange never evicts a past `q''ᵢ`"
- `no_nop_at_b2`: the last-repair analysis core — at a B2 position `t`
  (`d t ∈ D_t`), `t ∉ P`: `t = tᵢ` contradicts `hpast`, and `t = nᵢ`
  gives `d t = q''` (the value invariant `hcomp`) with `q'' ∉ D_t`
  (`evicted_page_absent_until_request`) — a no-op eviction, hence B1 not
  B2
- the case-step extension glue: `extend_hpast`, `extend_hQfifo`,
  `extend_hP`, `extend_hP_in`, `extend_hcomp`, `extend_hpair` (alive
  variants, `P' = P ∪ {t₂, t₂+1+j''}`) and `extend_hP_dead`,
  `extend_hP_in_dead`, `extend_hcomp_dead` (dead-page variants,
  `P' = P ∪ {t₂}`) — the composition invariants of the new state
  `Q' = insert (t₂, q'') Q`, `P'`, `r` from the old state's invariants
  plus the step's facts (`r t₂ = q''`, `r nop = q''`, `r s = d s` off
  `{t₂, nop}`, caches agree up to `t₂`, `σ[t₂]` fault, `q''` resident);
  hQ's extension is the open design question (see `Dev/DESIGN.md`)
- `iterate_main_case_b2_alive`: the case-B2 step (alive-alive) — the
  repair at a resident disagreement: agreement to `t₂ + 1`, misses not
  increased, chain extended by `q''`, `hd_eq` extended to
  `P ∪ {t₂, J''}`, reducedness bound `max hnb (J'' + 1)`
- `iterate_main_case_b1_alive`: the case-B1 step (alive) — the no-op
  repair: agreement to `t₂ + 1`, exact miss accounting
  `schedMisses r ≤ schedMisses d + bad` (the slack bookkeeping
  `slack − bad`), chain extended by `q''`, `hd_eq` extended to
  `P ∪ {t₂, J'''}`, reducedness bound `max hnb (J''' + 1)`;
  helpers `repair_q''_absent` (q'' stays out of the repair's cache on the
  window) and `repair_reverse_diff_after_nop` (reverse diff empty after
  `J'''`)
- `b2_hswap_qp_dead`: same for the `q''`-dead case — `repair_keep_swap_qp_dead`
  (B6), the dead-page repair `repairSchedule e t q'' t` still has the swap
  form at `J` (the good event for `repair_step_swap_qp_dead`)
- `iterate_main_exchange`: the case-A step of `iterate_main` — at the first
  disagreement `t`, the exchange extends agreement to `t + 1`, never
  increases misses (slack `+1` iff the bad event did not occur), and is
  reduced from `J' + 1` when `q'` is requested again
- the q₀'-B1 slack supply: `exchangeSchedule_eq_q'_imp_d_eq_q'` (the
  branch-1 reverse — the exchange evicts `q₀'` at `s > t₀` iff the source
  does), `b1_exchange_no_bad_q0` (at a B1 with `d t₂ = q₀'`, `t₂ ∉ P`,
  the source and the exchange both faulting at `t₂`: `t₂` is the first
  branch-1 of the window by `window_branch1_once`, the source's eviction
  of `q₀'` at `t₂` is real (`q₀' ∈ D₀_{t₂}` by the forward induction),
  and the `evicted_page_absent_until_request` induction (t₂ version)
  gives `q₀' ∉ D₀_{J'₀}` — the exchange's bad event did not occur) and
  `b1_bad_le_slack_q0` (`bad ≤ slack` for the q₀'-B1 given `1 ≤ slack`)
  — the q₀' half of the slack accounting; the non-q₀' B1s are the open
  design question (see `Dev/DESIGN.md`)

This file is part of the `fifo_optimal` iteration; it will be merged into
`S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

set_option maxHeartbeats 400000

/-- 桥接引理:活-活修复 `repairSchedule e t q'' (t + 1 + j'')` 的 nop 在
`J'' = t + 1 + j''` 处,而 `repair_cache_diff_le` 给的是死页修复
`repairSchedule e t q'' t`(nop 即 `t`)。在 `J = t + 1 + j` 之前
(`j < j''`)两个调度逐出相同(`t` 处都逐出 `q''`,其余都跟 `e`,nop 未触发),
故它们的 cache 一致。 -/
lemma schedCache_repairSchedule_nop_agree (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q'' : Page} {j j'' : ℕ} (hjj'' : j < j'') :
    ∀ s, s ≤ t + 1 + j →
      schedCache (repairSchedule e t q'' t) C₀ σ s =
          schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s := by
  intro s
  induction s with
  | zero => intro hs; rfl
  | succ s ih =>
      intro hs
      rw [schedCache, schedCache]
      rw [ih (by omega)]
      have hsch : repairSchedule e t q'' t s = repairSchedule e t q'' (t + 1 + j'') s := by
        unfold repairSchedule
        by_cases hst : s = t
        · simp [hst]
        · simp [hst, show s ≠ t + 1 + j'' by omega]
      rw [hsch]

/-- 活-活 B2 修复的窗口段:`J < s ≤ J''` 时,repair 的 cache 从源 `e` 的
cache 中只缺少 `q''`(反向差 `E − Ŝ ⊆ {q''}`)。基例 `J + 1` 处 `e` 于
`J` 缺页载入 `q`(好事件),`r` 命中(`hkept`),且 `E_J − Ŝ_J ⊆ {q, q''}`
(`repair_cache_diff_le` 于 `J`)中 `q ∉ E_J`(`swap_q_not_mem`),故只剩
`q''`。归纳步仅需 `r s = e s`(`s ∉ {t, J''}`)与 `σ[s] ≠ q''`。 -/
lemma repair_reverse_diff_window (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : e t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t + 1) q'' = some j'')
    (hjj'' : j < j'')
    (hkept : q ∈ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ (t + 1 + j)) :
    ∀ s, t + 1 + j < s → s ≤ t + 1 + j'' →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s ⊆
          ({q''} : Finset Page) := by
  let r : ℕ → Page := repairSchedule e t q'' (t + 1 + j'')
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  have hqnotE : ∀ s, t < s → s ≤ t + 1 + j → q ∉ E s := by
    intro s hs1 hs2
    exact swap_q_not_mem e σ C₀ hq hqin hft hj hs1 hs2
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hsJ hsJ''
      by_cases hs_eq : s = t + 1 + j
      · subst s
        -- 基例:J+1,e 于 J 缺页载入 q,r 命中(cache 不变)
        have hsigJ : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
        have hE' : E (t + 1 + j + 1) = insert q ((E (t + 1 + j)).erase (e (t + 1 + j))) := by
          dsimp [E]
          rw [schedCache]
          rw [hsigJ]
          rw [if_neg (hqnotE (t + 1 + j) (by omega) le_rfl)]
        have hS' : S (t + 1 + j + 1) = S (t + 1 + j) := by
          dsimp [S]
          rw [schedCache]
          rw [hsigJ]
          rw [if_pos hkept]
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_singleton]
        have hxE : x ∈ insert q ((E (t + 1 + j)).erase (e (t + 1 + j))) := by
          rw [← hE']
          exact hx.1
        have hxnotS : x ∉ S (t + 1 + j) := by
          intro hxS
          exact hx.2 (by change x ∈ S (t + 1 + j + 1); rw [hS']; exact hxS)
        rcases Finset.mem_insert.mp hxE with hxr | hxE2
        · -- x = q:q ∈ Ŝ_J(hkept)矛盾
          exfalso
          exact hxnotS (hxr ▸ hkept)
        · -- x ∈ E_J − e J,x ∉ Ŝ_J:E_J − Ŝ_J ⊆ {q,q''}(J 处),q ∉ E_J
          have hxin : x ∈ E (t + 1 + j) := (Finset.mem_erase.mp hxE2).2
          have hdead : ∀ s, t < s → s < t + 1 + j → σ.getD s 0 ∉ ({q, q''} : Finset Page) := by
            intro s hs1 hs2 hm
            rcases Finset.mem_insert.mp hm with hqeq | hq''eq
            · exact getD_ne_nextUse (k := s) hj (by omega) (by omega) hqeq
            · exact getD_ne_nextUse (k := s) hj'' (by omega) (by omega)
                (Finset.mem_singleton.mp hq''eq)
          have hdiffJ := repair_cache_diff_le e σ C₀ hq hq'' hft hqq'' hj hdead (t + 1 + j) le_rfl
          have hxqq'' : x ∈ ({q, q''} : Finset Page) := hdiffJ.2 (by
            rw [Finset.mem_sdiff]
            rw [schedCache_repairSchedule_nop_agree e σ C₀ hjj'' (t + 1 + j) le_rfl]
            exact ⟨hxin, hxnotS⟩)
          rcases Finset.mem_insert.mp hxqq'' with hxq | hxq''
          · exfalso
            exact hqnotE (t + 1 + j) (by omega) le_rfl (hxq ▸ hxin)
          · exact Finset.mem_singleton.mp hxq''
      · -- 归纳步:J < s
        have hsJ' : t + 1 + j < s := by omega
        have hih := ih hsJ' (by omega)
        have hs_ne_t : s ≠ t := by omega
        have hs_ne_J'' : s ≠ t + 1 + j'' := by omega
        have hrs : r s = e s := by
          unfold r repairSchedule
          simp [hs_ne_t, hs_ne_J'']
        have hsig_ne_q'' : σ.getD s 0 ≠ q'' := by
          exact getD_ne_nextUse (k := s) hj'' (by omega) (by omega)
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_singleton]
        rw [schedCache, schedCache] at hx
        rw [show (repairSchedule e t q'' (t + 1 + j'')) s = e s by exact hrs] at hx
        by_cases he : σ.getD s 0 ∈ E s
        · -- e 命中 ⟹ r 命中(否则 σ[s] ∈ E − Ŝ ⊆ {q''},σ[s] = q'' 矛盾)
          rw [if_pos he] at hx
          have hr' : σ.getD s 0 ∈ S s := by
            by_contra hnot
            have hmem : σ.getD s 0 ∈ E s \ S s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hnot⟩
            exact hsig_ne_q'' (Finset.mem_singleton.mp (hih hmem))
          rw [if_pos hr'] at hx
          have hmem : x ∈ E s \ S s := by
            rw [Finset.mem_sdiff]
            exact ⟨hx.1, hx.2⟩
          exact Finset.mem_singleton.mp (hih hmem)
        · -- e 缺页
          rw [if_neg he] at hx
          by_cases hr' : σ.getD s 0 ∈ S s
          · -- r 命中:Ŝ 不变,E 载入 σ[s] 逐出 e s
            rw [if_pos hr'] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE2
            · exfalso
              exact hx.2 (hxr ▸ hr')
            · have hxin : x ∈ E s := (Finset.mem_erase.mp hxE2).2
              have hmem : x ∈ E s \ S s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, hx.2⟩
              exact Finset.mem_singleton.mp (hih hmem)
          · -- 双缺页
            rw [if_neg hr'] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE2
            · exfalso
              exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
            · have hxin : x ∈ E s := (Finset.mem_erase.mp hxE2).2
              have hxne : x ≠ e s := (Finset.mem_erase.mp hxE2).1
              have hmem : x ∈ E s \ S s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, by
                  intro hxS
                  by_cases hxeq : x = σ.getD s 0
                  · exact he (hxeq ▸ hxin)
                  · exact hx.2 (Finset.mem_insert.mpr
                      (Or.inr (Finset.mem_erase.mpr ⟨hxne, hxS⟩)))⟩
              exact Finset.mem_singleton.mp (hih hmem)

/-- 活-活 B2 修复的 `J''` 之后:`E_s ⊆ Ŝ_s`(反向差为空)。基例 `J'' + 1`
处双方都得到 `q''`(e 命中或载入,r 载入——nop 逐出 `q''` 是 no-op),且
`E_{J''} − Ŝ_{J''} ⊆ {q''}`(`hw` 于 `J''`)中 `q'' ∉ E − Ŝ`(双方都有
`q''`);归纳步 `r s = e s` 保持包含关系。 -/
lemma repair_reverse_diff_after (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : e t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t + 1) q'' = some j'')
    (hjj'' : j < j'')
    (hkept : q ∈ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ (t + 1 + j))
    (hw : ∀ s, t + 1 + j < s → s ≤ t + 1 + j'' →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s ⊆
          ({q''} : Finset Page)) :
    ∀ s, t + 1 + j'' < s → s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s = ∅ := by
  let r : ℕ → Page := repairSchedule e t q'' (t + 1 + j'')
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hsJ'' hslen
      by_cases hs_eq : s = t + 1 + j''
      · subst s
        -- 基例:J''+1,请求 q''
        change E (t + 1 + j'' + 1) \ S (t + 1 + j'' + 1) = ∅
        have hsig : σ.getD (t + 1 + j'') 0 = q'' := getD_eq_nextUse hj''
        have hEcase : E (t + 1 + j'' + 1) =
            (if σ.getD (t + 1 + j'') 0 ∈ E (t + 1 + j'') then E (t + 1 + j'')
             else insert (σ.getD (t + 1 + j'') 0) ((E (t + 1 + j'')).erase (e (t + 1 + j'')))) := by
          dsimp [E]
          rw [schedCache]
        have hScase : S (t + 1 + j'' + 1) =
            (if σ.getD (t + 1 + j'') 0 ∈ S (t + 1 + j'') then S (t + 1 + j'')
             else insert (σ.getD (t + 1 + j'') 0) ((S (t + 1 + j'')).erase q'')) := by
          dsimp [S]
          rw [schedCache]
          unfold r repairSchedule
          simp
        by_cases he : σ.getD (t + 1 + j'') 0 ∈ E (t + 1 + j'')
        · rw [hEcase, if_pos he]
          by_cases hr' : σ.getD (t + 1 + j'') 0 ∈ S (t + 1 + j'')
          · -- 双命中
            rw [hScase, if_pos hr']
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Finset.mem_sdiff] at hx
            have hmem : x ∈ E (t + 1 + j'') \ S (t + 1 + j'') := by
              rw [Finset.mem_sdiff]
              exact ⟨hx.1, hx.2⟩
            have hxq'' : x = q'' := Finset.mem_singleton.mp (hw (t + 1 + j'') (by omega) le_rfl hmem)
            exact hx.2 (hxq''.symm ▸ (hsig ▸ hr'))
          · -- e 命中,r 缺页(nop 逐出 no-op,Ŝ 载入 q'')
            rw [hScase, if_neg hr']
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Finset.mem_sdiff] at hx
            by_cases hxq'' : x = q''
            · exact hx.2 (by
                rw [hsig, hxq'']
                exact Finset.mem_insert_self _ _)
            · have hmem : x ∈ E (t + 1 + j'') \ S (t + 1 + j'') := by
                rw [Finset.mem_sdiff]
                exact ⟨hx.1, by
                  intro hxS
                  exact hx.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxq'', hxS⟩)))⟩
              have hxq := Finset.mem_singleton.mp (hw (t + 1 + j'') (by omega) le_rfl hmem)
              exact hxq'' hxq
        · -- e 缺页
          rw [hEcase, if_neg he]
          by_cases hr' : σ.getD (t + 1 + j'') 0 ∈ S (t + 1 + j'')
          · -- e 缺页,r 命中
            rw [hScase, if_pos hr']
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Finset.mem_sdiff] at hx
            by_cases hxq'' : x = σ.getD (t + 1 + j'') 0
            · exact hx.2 (by rw [hxq'']; exact hr')
            · have hmem : x ∈ E (t + 1 + j'') \ S (t + 1 + j'') := by
                rw [Finset.mem_sdiff]
                exact ⟨by
                  rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                  · exfalso
                    exact hxq'' hxp
                  · exact (Finset.mem_erase.mp hxE2).2, hx.2⟩
              have hxq := Finset.mem_singleton.mp (hw (t + 1 + j'') (by omega) le_rfl hmem)
              exfalso
              exact hxq'' (hxq.trans hsig.symm)
          · -- 双缺页
            rw [hScase, if_neg hr']
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Finset.mem_sdiff] at hx
            by_cases hxq'' : x = σ.getD (t + 1 + j'') 0
            · exact hx.2 (by
                rw [hxq'']
                exact Finset.mem_insert_self _ _)
            · have hmem : x ∈ E (t + 1 + j'') \ S (t + 1 + j'') := by
                rw [Finset.mem_sdiff]
                exact ⟨by
                  rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                  · exfalso
                    exact hxq'' hxp
                  · exact (Finset.mem_erase.mp hxE2).2, by
                  intro hxS
                  exact hx.2 (by
                    rw [← hsig]
                    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxq'', hxS⟩)))⟩
              have hxq := Finset.mem_singleton.mp (hw (t + 1 + j'') (by omega) le_rfl hmem)
              exact hx.2 (by
                rw [hxq, ← hsig]
                exact Finset.mem_insert_self _ _)
      · -- 归纳步:J'' < s
        have hsJ'' : t + 1 + j'' < s := by omega
        have hih := ih hsJ'' (by omega)
        have hs_ne_t : s ≠ t := by omega
        have hs_ne_J'' : s ≠ t + 1 + j'' := by omega
        have hrs : r s = e s := by
          unfold r repairSchedule
          simp [hs_ne_t, hs_ne_J'']
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [schedCache, schedCache] at hx
        rw [show (repairSchedule e t q'' (t + 1 + j'')) s = e s by exact hrs] at hx
        by_cases he : σ.getD s 0 ∈ E s
        · -- e 命中 ⟹ r 命中(E_s ⊆ Ŝ_s)
          rw [if_pos he] at hx
          have hr' : σ.getD s 0 ∈ S s := by
            by_contra hnot
            have hmem : σ.getD s 0 ∈ E s \ S s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hnot⟩
            exact (Finset.notMem_empty (σ.getD s 0)) (hih ▸ hmem)
          rw [if_pos hr'] at hx
          exact (Finset.notMem_empty x) (hih ▸ (by
            rw [Finset.mem_sdiff]
            exact ⟨hx.1, hx.2⟩))
        · -- e 缺页
          rw [if_neg he] at hx
          by_cases hr' : σ.getD s 0 ∈ S s
          · -- r 命中:Ŝ 不变,E 载入
            rw [if_pos hr'] at hx
            exact (Finset.notMem_empty x) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hx.2 (hxp.symm ▸ hr')
                · exact (Finset.mem_erase.mp hxE2).2, hx.2⟩))
          · -- 双缺页
            rw [if_neg hr'] at hx
            exact (Finset.notMem_empty x) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hx.2 (Finset.mem_insert.mpr (Or.inl hxp))
                · exact (Finset.mem_erase.mp hxE2).2, by
                  intro hxS
                  by_cases hxeq : x = σ.getD s 0
                  · exfalso
                    exact hx.2 (Finset.mem_insert.mpr (Or.inl hxeq))
                  · rcases Finset.mem_insert.mp hx.1 with hxp | hxE2'
                    · exfalso
                      exact hxeq hxp
                    · exact hx.2 (Finset.mem_insert.mpr
                        (Or.inr (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxE2').1, hxS⟩)))⟩))

/-- 活-活 B2 修复的完整反向差:`∀ s ≤ σ.length`,repair 的 cache 从源
`e` 的 cache 中只缺少 `{q, q''}` 中的页;`J < s` 时只缺少 `q''`;
`J'' < s` 时不再缺少(`E_s ⊆ Ŝ_s`)。 -/
lemma repair_diff_all (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : e t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t + 1) q'' = some j'')
    (hjj'' : j < j'')
    (hkept : q ∈ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ (t + 1 + j)) :
    ∀ s, s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s ⊆
          ({q, q''} : Finset Page) ∧
      (t + 1 + j < s →
        schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s ⊆
            ({q''} : Finset Page)) ∧
      (t + 1 + j'' < s →
        schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s = ∅) := by
  let r : ℕ → Page := repairSchedule e t q'' (t + 1 + j'')
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  have hw : ∀ s, t + 1 + j < s → s ≤ t + 1 + j'' →
      E s \ S s ⊆ ({q''} : Finset Page) := by
    intro s hs1 hs2
    exact repair_reverse_diff_window e σ C₀ hq hq'' hqin hft hqq'' hj hj'' hjj'' hkept s hs1 hs2
  have ha : ∀ s, t + 1 + j'' < s → s ≤ σ.length → E s \ S s = ∅ := by
    intro s hs1 hs2
    exact repair_reverse_diff_after e σ C₀ hq hq'' hqin hft hqq'' hj hj'' hjj'' hkept hw s hs1 hs2
  intro s hslen
  by_cases hsJ : s ≤ t + 1 + j
  · -- s ≤ J:repair_cache_diff_le(构造 hdead)
    have hdead : ∀ s, t < s → s < t + 1 + j → σ.getD s 0 ∉ ({q, q''} : Finset Page) := by
      intro s hs1 hs2 hm
      rcases Finset.mem_insert.mp hm with hqeq | hq''eq
      · exact getD_ne_nextUse (k := s) hj (by omega) (by omega) hqeq
      · exact getD_ne_nextUse (k := s) hj'' (by omega) (by omega)
          (Finset.mem_singleton.mp hq''eq)
    have hdiff := repair_cache_diff_le e σ C₀ hq hq'' hft hqq'' hj hdead s hsJ
    constructor
    · rw [show schedCache (repairSchedule e t q'' (t + 1 + j'')) C₀ σ s =
          schedCache (repairSchedule e t q'' t) C₀ σ s by
        exact (schedCache_repairSchedule_nop_agree e σ C₀ hjj'' s hsJ).symm]
      exact hdiff.2
    · constructor
      · intro hs1
        exfalso
        omega
      · intro hs1
        exfalso
        omega
  · -- J < s
    have hsJ' : t + 1 + j < s := by omega
    constructor
    · intro x hx
      have hmem : x ∈ E s \ S s := hx
      by_cases hsJ'' : s ≤ t + 1 + j''
      · -- (J, J'']:⊆ {q''} ⊆ {q, q''}
        have hxq'' : x = q'' := Finset.mem_singleton.mp (hw s hsJ' hsJ'' hx)
        rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_singleton.mpr hxq'')
      · -- J'' < s:∅
        have hsJ'' : t + 1 + j'' < s := by omega
        have hempty : E s \ S s = ∅ := ha s hsJ'' hslen
        exfalso
        exact (Finset.notMem_empty x) (hempty ▸ hx)
    · constructor
      · intro hs1
        by_cases hsJ'' : s ≤ t + 1 + j''
        · exact hw s hsJ' hsJ''
        · rw [ha s (by omega) hslen]
          simp
      · intro hs1
        exact ha s hs1 hslen

/-- 反向差链:链不变式 `E − D ⊆ Q`(参考调度 `e` 与迭代 `d` 的反向差)在
活-活 B2 修复 `r = repairSchedule d t q'' (t + 1 + j'')` 之后只增加 `q''`:
`E − Ŝ ⊆ insert q'' Q` 对所有 `s ≤ σ.length` 成立。`x ∈ E − Ŝ` 按
`x ∈ D` 与否分成 `E − D ⊆ Q`(`hchain`)与 `D − Ŝ ⊆ {q, q''}`
(`repair_diff_all`)两枝;`x = q` 与 `q ∉ E`(`hqnotE`,窗口 `(t, J]` 上
`e` 于 `t` 逐出 `q`)矛盾,故只剩 `q''`。 -/
lemma reverse_diff_chain (e : ℕ → Page) (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : d t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache d C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t + 1) q'' = some j'')
    (hjj'' : j < j'')
    (hkept : q ∈ schedCache (repairSchedule d t q'' (t + 1 + j'')) C₀ σ (t + 1 + j))
    (Q : Finset Page)
    (hqnotE : ∀ s, t < s → s ≤ t + 1 + j → q ∉ schedCache e C₀ σ s)
    (hchain : ∀ s, s ≤ σ.length → schedCache e C₀ σ s \ schedCache d C₀ σ s ⊆ Q) :
    ∀ s, s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule d t q'' (t + 1 + j'')) C₀ σ s ⊆
          insert q'' Q := by
  let r : ℕ → Page := repairSchedule d t q'' (t + 1 + j'')
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let D : ℕ → Finset Page := schedCache d C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  have hdiff : ∀ s, s ≤ σ.length →
      D s \ S s ⊆ ({q, q''} : Finset Page) ∧
      (t + 1 + j < s → D s \ S s ⊆ ({q''} : Finset Page)) ∧
      (t + 1 + j'' < s → D s \ S s = ∅) := by
    intro s hslen
    exact repair_diff_all d σ C₀ hq hq'' hqin hft hqq'' hj hj'' hjj'' hkept s hslen
  intro s hslen
  intro x hx
  rw [Finset.mem_sdiff] at hx
  by_cases hst : s ≤ t
  · -- s ≤ t:r 与 d 的 cache 相同(S = D),故 x ∉ S ⟹ x ∉ D ⟹ x ∈ E − D ⊆ Q
    have hSD : S s = D s := by
      dsimp [S, D]
      exact schedCache_repairSchedule_eq_e d t q'' (t + 1 + j'') (by omega) σ C₀ hst
    rw [Finset.mem_insert]
    exact Or.inr (hchain s hslen (by
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, by
        intro hxD
        exact hx.2 (by change x ∈ S s; rw [hSD]; exact hxD)⟩))
  · -- t < s
    have hts : t < s := by omega
    by_cases hxD : x ∈ D s
    · -- x ∈ D:x ∈ D − Ŝ ⊆ {q, q''}(或窗口内的 {q''})
      have hmem : x ∈ D s \ S s := by
        rw [Finset.mem_sdiff]
        exact ⟨hxD, hx.2⟩
      by_cases hsJ : s ≤ t + 1 + j
      · -- s ≤ J:⊆ {q,q''};x = q 与 q ∉ E 矛盾
        rw [Finset.mem_insert]
        have hxqq'' := (hdiff s hslen).1 hmem
        rcases Finset.mem_insert.mp hxqq'' with hxq | hxq''
        · exfalso
          exact hqnotE s hts hsJ (hxq ▸ hx.1)
        · exact Or.inl (Finset.mem_singleton.mp hxq'')
      · -- J < s:窗口内 ⊆ {q''},J'' 后为空
        have hsJ' : t + 1 + j < s := by omega
        by_cases hsJ'' : s ≤ t + 1 + j''
        · rw [Finset.mem_insert]
          have hxq'' := Finset.mem_singleton.mp ((hdiff s hslen).2.1 hsJ' hmem)
          exact Or.inl hxq''
        · have hsJ'' : t + 1 + j'' < s := by omega
          exfalso
          exact (Finset.notMem_empty x) ((hdiff s hslen).2.2 hsJ'' ▸ hmem)
    · -- x ∉ D:x ∈ E − D ⊆ Q
      rw [Finset.mem_insert]
      exact Or.inr (hchain s hslen (by
        rw [Finset.mem_sdiff]
        exact ⟨hx.1, hxD⟩))

/-- 反向差链(q'' 死版):`q''` 永不再请求的 B2 修复
`r = repairSchedule d t q'' t` 之后,链不变式 `E − D ⊆ Q` 只增加 `q''`。
与 `reverse_diff_chain` 同构,但差集用死页引理:`s ≤ J` 处
`repair_cache_diff_le`(`D − Ŝ ⊆ {q, q''}`,`x = q` 与 `hqnotE` 矛盾),
`J` 后 `repair_cache_diff_after`(`D − Ŝ ⊆ {q''}`,不再需要排除 `q`)。 -/
lemma reverse_diff_chain_qp_dead (e : ℕ → Page) (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : d t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache d C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq''dead : nextUse σ (t + 1) q'' = none)
    (hkept : q ∈ schedCache (repairSchedule d t q'' t) C₀ σ (t + 1 + j))
    (Q : Finset Page)
    (hqnotE : ∀ s, t < s → s ≤ t + 1 + j → q ∉ schedCache e C₀ σ s)
    (hchain : ∀ s, s ≤ σ.length → schedCache e C₀ σ s \ schedCache d C₀ σ s ⊆ Q) :
    ∀ s, s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule d t q'' t) C₀ σ s ⊆
          insert q'' Q := by
  let r : ℕ → Page := repairSchedule d t q'' t
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let D : ℕ → Finset Page := schedCache d C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  have hdiff_le : ∀ s, s ≤ t + 1 + j →
      S s \ D s ⊆ ({q, q''} : Finset Page) ∧ D s \ S s ⊆ ({q, q''} : Finset Page) := by
    intro s hsJ
    exact repair_cache_diff_le d σ C₀ hq hq'' hft hqq'' hj
      (repair_requests_avoid_q_qp σ hj hq''dead) s hsJ
  have hdiff_after : ∀ s, t + 1 + j < s → s ≤ σ.length → D s \ S s ⊆ ({q''} : Finset Page) := by
    intro s hsJ hslen
    exact repair_cache_diff_after d σ C₀ hq hq'' hqin hft hqq'' hj
      hq''dead hkept hdiff_le s hsJ hslen
  intro s hslen
  intro x hx
  rw [Finset.mem_sdiff] at hx
  by_cases hst : s ≤ t
  · -- s ≤ t:r 与 d 的 cache 相同(S = D),故 x ∉ S ⟹ x ∉ D ⟹ x ∈ E − D ⊆ Q
    have hSD : S s = D s := by
      dsimp [S, D]
      exact schedCache_repairSchedule_eq_e_qp_dead d t q'' σ C₀ hst
    rw [Finset.mem_insert]
    exact Or.inr (hchain s hslen (by
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, by
        intro hxD
        exact hx.2 (by change x ∈ S s; rw [hSD]; exact hxD)⟩))
  · -- t < s
    have hts : t < s := by omega
    by_cases hsJ : s ≤ t + 1 + j
    · -- s ≤ J:x ∈ D − Ŝ ⊆ {q, q''},x = q 与 hqnotE 矛盾
      by_cases hxD : x ∈ D s
      · have hmem : x ∈ D s \ S s := by
          rw [Finset.mem_sdiff]
          exact ⟨hxD, hx.2⟩
        rw [Finset.mem_insert]
        have hxqq'' := (hdiff_le s hsJ).2 hmem
        rcases Finset.mem_insert.mp hxqq'' with hxq | hxq''
        · exfalso
          exact hqnotE s hts hsJ (hxq ▸ hx.1)
        · exact Or.inl (Finset.mem_singleton.mp hxq'')
      · -- x ∉ D:x ∈ E − D ⊆ Q
        rw [Finset.mem_insert]
        exact Or.inr (hchain s hslen (by
          rw [Finset.mem_sdiff]
          exact ⟨hx.1, hxD⟩))
    · -- J < s:D − Ŝ ⊆ {q''}
      have hsJ' : t + 1 + j < s := by omega
      by_cases hxD : x ∈ D s
      · have hmem : x ∈ D s \ S s := by
          rw [Finset.mem_sdiff]
          exact ⟨hxD, hx.2⟩
        rw [Finset.mem_insert]
        exact Or.inl (Finset.mem_singleton.mp (hdiff_after s hsJ' hslen hmem))
      · -- x ∉ D:x ∈ E − D ⊆ Q
        rw [Finset.mem_insert]
        exact Or.inr (hchain s hslen (by
          rw [Finset.mem_sdiff]
          exact ⟨hx.1, hxD⟩))

/-- 反向差链(q 死版):`q`、`q''` 都永不再请求的 B2 修复
`r = repairSchedule d t q'' t` 之后,链不变式 `E − D ⊆ Q` 只增加 `q''`。
`D − Ŝ ⊆ {q, q''}` 处处成立(`repair_cache_diff`,无界 `hdead`),`x = q`
与 `hqnotE`(调用方从 `swap_q_not_mem_dead` 得到)矛盾。 -/
lemma reverse_diff_chain_q_dead (e : ℕ → Page) (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : d t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache d C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hqq'' : q ≠ q'')
    (hqdead : nextUse σ (t + 1) q = none)
    (hq''dead : nextUse σ (t + 1) q'' = none)
    (Q : Finset Page)
    (hqnotE : ∀ s, t < s → s ≤ σ.length → q ∉ schedCache e C₀ σ s)
    (hchain : ∀ s, s ≤ σ.length → schedCache e C₀ σ s \ schedCache d C₀ σ s ⊆ Q) :
    ∀ s, s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule d t q'' t) C₀ σ s ⊆
          insert q'' Q := by
  let r : ℕ → Page := repairSchedule d t q'' t
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let D : ℕ → Finset Page := schedCache d C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  have hdead : ∀ s, t < s → s < σ.length → σ.getD s 0 ∉ ({q, q''} : Finset Page) := by
    intro s hst hslen hmem
    rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
    · exact getD_ne_of_nextUse_none σ hqdead (by omega) hslen hqeq
    · exact getD_ne_of_nextUse_none σ hq''dead (by omega) hslen
        (Finset.mem_singleton.mp hq'eq)
  have hdiff : ∀ s, s ≤ σ.length →
      S s \ D s ⊆ ({q, q''} : Finset Page) ∧ D s \ S s ⊆ ({q, q''} : Finset Page) := by
    intro s hslen
    exact repair_cache_diff d σ C₀ hq hq'' hft hqq'' hdead s hslen
  intro s hslen
  intro x hx
  rw [Finset.mem_sdiff] at hx
  by_cases hst : s ≤ t
  · -- s ≤ t:r 与 d 的 cache 相同(S = D),故 x ∉ S ⟹ x ∉ D ⟹ x ∈ E − D ⊆ Q
    have hSD : S s = D s := by
      dsimp [S, D]
      exact schedCache_repairSchedule_eq_e_qp_dead d t q'' σ C₀ hst
    rw [Finset.mem_insert]
    exact Or.inr (hchain s hslen (by
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, by
        intro hxD
        exact hx.2 (by change x ∈ S s; rw [hSD]; exact hxD)⟩))
  · -- t < s
    have hts : t < s := by omega
    by_cases hxD : x ∈ D s
    · -- x ∈ D:x ∈ D − Ŝ ⊆ {q, q''},x = q 与 hqnotE 矛盾
      have hmem : x ∈ D s \ S s := by
        rw [Finset.mem_sdiff]
        exact ⟨hxD, hx.2⟩
      rw [Finset.mem_insert]
      have hxqq'' := (hdiff s hslen).2 hmem
      rcases Finset.mem_insert.mp hxqq'' with hxq | hxq''
      · exfalso
        exact hqnotE s hts hslen (hxq ▸ hx.1)
      · exact Or.inl (Finset.mem_singleton.mp hxq'')
    · -- x ∉ D:x ∈ E − D ⊆ Q
      rw [Finset.mem_insert]
      exact Or.inr (hchain s hslen (by
        rw [Finset.mem_sdiff]
        exact ⟨hx.1, hxD⟩))

/-- B2 e-hit 引理(单步局部形式,Huffman 交换论证风格):在分歧位置 `t` 处,
`d` 缺页(`hft`),且反向差链在 `t` 的实例
`E_t − D_t ⊆ Q`(`hchain`,由 `reverse_diff_chain` 逐点给出)成立时,请求
`σ[t]` 命中参考调度 `e` 的 cache 会把它压进 `Q`:`σ[t] ∈ E_t ⟹ σ[t] ∈ Q`。
这是 DESIGN 中 b2_ehit 机制的第一步 —— 只做位置 `t` 的局部一步,不做全局
的 `Q''` 追踪(链不变式封装了全局部分)。`σ[t] ∈ Q` 与 "死页或未请求"
的矛盾由 `b2_ehit_ne` 处理。经验验证:search_iter.py 的 search3 在 55188 个
B2 位置上 e-hit = 0。 -/
lemma b2_ehit (e d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (Q : Finset Page)
    (hchain : schedCache e C₀ σ t \ schedCache d C₀ σ t ⊆ Q) :
    σ.getD t 0 ∈ schedCache e C₀ σ t → σ.getD t 0 ∈ Q := by
  intro he
  exact hchain (by
    rw [Finset.mem_sdiff]
    exact ⟨he, hft⟩)

/-- B2 e-hit 引理的矛盾半边:过往修复对集合 `Q ⊆ ℕ × Page`(元素为
`(tᵢ, q''ᵢ)`,修复位置与修复页)中每个 `q''ᵢ` 都是死页(`nextUse σ (tᵢ+1)
q''ᵢ = none`)或在 `t` 处尚未请求(`t < tᵢ + 1 + j''ᵢ`)时,请求 `σ[t]`
不属于 `Q` 的页集:`σ[t] ∉ Q.image Prod.snd`。死页用 `getD_ne_of_nextUse_none`
(B6),未请求用 `getD_ne_nextUse`。经验验证:分歧位置上请求属于过往修复页
共 8976 次、全部发生在 `t = J''ᵢ`(B1 nop 位置),B2 上为 0 次 —— 本引理
覆盖死页与 `t < J''ᵢ` 两枝,`t = J''ᵢ` 枝(B1 而非 B2)留给 `iterate_main`。 -/
lemma b2_ehit_ne (σ : List Page) {t : ℕ} (ht : t < σ.length)
    (Q : Finset (ℕ × Page))
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t < tᵢ + 1 + j'') :
    σ.getD t 0 ∉ Q.image Prod.snd := by
  intro hsigQ
  rcases Finset.mem_image.mp hsigQ with ⟨⟨tᵢ, q''⟩, htq, hsigq⟩
  have htlt : tᵢ < t := hpast tᵢ q'' htq
  rcases hQ tᵢ q'' htq with hdead | ⟨j'', hnext, htltJ⟩
  · -- 死页:σ[t] = q'' 与 `q''` 在 tᵢ 之后永不请求矛盾
    exact getD_ne_of_nextUse_none σ hdead (by omega) ht hsigq.symm
  · -- 未请求:t < J''ᵢ 处请求 σ[t] = q'' 与首次请求在 J''ᵢ 矛盾
    exact getD_ne_nextUse (k := t) hnext (by omega) htltJ hsigq.symm

/-- keep-swap 核心(当前调度的 `b2_no_evict_q`):在 B2 位置 `t` 的窗口
`(t, J]` 内,对 `e` 的每个缺页位置 `s`:
- `d s = e s` —— 位置 `s` 不是过往修复/nop 位置(`hnot`,由 `P` 记录;
  组成不变式 `hd_eq` 给出 `P` 之外的逐出一致),经验上 136 个窗口在
  `(t, J]` 内有过往修复/nop 位置、其中 12 个是 `e` 的缺页且 `d s ≠ e s`,
  故 `hnot` 必不可少;
- `e s ≠ q` —— `exchange_no_evict_q` 的实例化,其 `hft₂`(e 于 `t` 缺页)
  由 `b2_ehit`(链 `hchain` 于 `t` 的实例压 `σ[t] ∈ E_t` 进 `Q.image
  Prod.snd`)+ `b2_ehit_ne`(死页或未请求的矛盾)推出;`hqin`(`q ∈ E_t`)
  来自 `e t = q` 的分支分析(调用方提供)。 -/
lemma b2_no_evict_q (d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d C₀ σ t₀)
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t : ℕ} (ht : t < σ.length) (ht₀t : t₀ < t) (htt' : t < t₀ + 1 + j₀')
    {q : Page} (hq : (exchangeSchedule d t₀ q₀ q₀' σ C₀) t = q)
    (hqin : q ∈ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t)
    (hftd : σ.getD t 0 ∉ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (Q : Finset (ℕ × Page))
    (hchain : schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t \
        schedCache d C₀ σ t ⊆ Q.image Prod.snd)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t < tᵢ + 1 + j'')
    (P : Finset ℕ)
    (hnot : ∀ s, t < s → s ≤ t + 1 + j → s ∉ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d t₀ q₀ q₀' σ C₀) s) :
    ∀ s, t < s → s ≤ t + 1 + j →
      σ.getD s 0 ∉ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ s →
        d s = (exchangeSchedule d t₀ q₀ q₀' σ C₀) s ∧
          (exchangeSchedule d t₀ q₀ q₀' σ C₀) s ≠ q := by
  let e : ℕ → Page := exchangeSchedule d t₀ q₀ q₀' σ C₀
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t := by
    intro he
    exact (b2_ehit_ne σ ht Q hpast hQ) (b2_ehit e d σ C₀ hftd (Q.image Prod.snd) hchain he)
  intro s hs1 hs2 hFault
  constructor
  · exact hd_eq s (hnot s hs1 hs2)
  · exact exchange_no_evict_q d t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
      ht₀t htt' hq hqin hft hj (s := s) hs1 hs2 hFault

/-- B2 的 keep-swap 形式(当前窗口):B6 `repair_keep_swap` 在迭代上下文的
实例化 —— 窗口参数 `(t₀, q₀, q₀', j₀')` 与 B2 位置 `t` 的局部事实
(`hagree`/`hdis` 来自 `first_disagree` 的窗口版,`hqin` 是 B2 常驻,
`hj`/`hj''`/`hjj''` 是活-活情形)给出好事件 `J = t + 1 + j` 处的 swap 形式:
`Ŝ_J = insert q (E_J − q'')`。仅实例化,无新证明。 -/
lemma b2_hswap (d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t : ℕ} (ht : t < σ.length) (ht₀t : t₀ < t) (htt' : t < t₀ + 1 + j₀')
    (hagree : agreeWithFIF (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t)
    (hdis : schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t + 1) ≠
      schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    {q : Page} (hq : (exchangeSchedule d t₀ q₀ q₀' σ C₀) t = q)
    (hqin : q ∈ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t)
    {j'' : ℕ} (hj'' : nextUse σ (t + 1) q'' = some j'')
    (hjj'' : j < j'') :
    schedCache (repairSchedule (exchangeSchedule d t₀ q₀ q₀' σ C₀) t q'' (t + 1 + j'')) C₀ σ (t + 1 + j) =
      insert q ((schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t + 1 + j)).erase q'') := by
  subst hq''
  simpa [hq] using repair_keep_swap d t₀ q₀ q₀' σ C₀ hC₀ hq₀ hqq₀ hweak hft₀ hq₀'res hj₀ hq₀'ne hj₀'
    ht ht₀t htt' hagree hdis (by simpa [← hq] using hqin) (by simpa [← hq] using hj) hj'' hjj''

/-- B2 的 keep-swap 形式(q'' 死版):`repair_keep_swap_qp_dead`(B6)在迭代
上下文的实例化 —— `q''` 永不再请求时,死页修复 `r = repairSchedule e t q'' t`
的好事件 `J = t + 1 + j` 处仍有 swap 形式 `Ŝ_J = insert q (E_J − q'')`
(给出 `repair_step_swap_qp_dead` 所需的 `q ∈ Ŝ_J`)。仅实例化,无新证明。 -/
lemma b2_hswap_qp_dead (d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t : ℕ} (ht : t < σ.length) (ht₀t : t₀ < t) (htt' : t < t₀ + 1 + j₀')
    (hagree : agreeWithFIF (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t)
    (hdis : schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t + 1) ≠
      schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    {q : Page} (hq : (exchangeSchedule d t₀ q₀ q₀' σ C₀) t = q)
    (hqin : q ∈ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t)
    (hq''dead : nextUse σ (t + 1) q'' = none) :
    schedCache (repairSchedule (exchangeSchedule d t₀ q₀ q₀' σ C₀) t q'' t) C₀ σ (t + 1 + j) =
      insert q ((schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t + 1 + j)).erase q'') := by
  subst hq''
  simpa [hq] using repair_keep_swap_qp_dead d t₀ q₀ q₀' σ C₀ hC₀ hq₀ hqq₀ hweak hft₀ hq₀'res hj₀ hq₀'ne hj₀'
    ht ht₀t htt' hagree hdis (by simpa [← hq] using hqin) (by simpa [← hq] using hj) hq''dead

/-- keep-swap 推导(当前调度版):B2 位置 `t₂` 处的修复作用于**当前**调度
`d`(交换调度 `e = exchangeSchedule d_pre t₀ q₀ q₀' σ C₀` 加过往修复),而非
纯交换调度。swap 形式 `Ŝ = insert q (D − q'')` 在 `(t₂, J]` 上保持(尤其到
`J` —— 好事件)。与 `repair_keep_swap` 同构,但 `d s ≠ q` 由 `hd_eq`(off
`P` 处 `d = e`)+ `hnot`(窗口内无过往修改位置)+ `exchange_no_evict_q` 给出;
`e` 于 `t₂` 缺页由 `b2_ehit` + `b2_ehit_ne` 从链 `hchain` 推出;
窗口内 `e` 缺页(`σ[s] ∉ E_s`)由 `hnotE` 给出(Q'' 排除论证,见 DESIGN);
`hqinE`(`q` 在交换调度 `t₂` 的 cache 中)是分支分析(`b2_no_evict_q` 注释)。 -/
lemma repair_keep_swap_cur (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d_pre t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s →
      d_pre s ∈ schedCache d_pre C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d_pre C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : d t₂ ∈ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (d t₂) = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j'')
    (hjj'' : j < j'')
    (Q : Finset (ℕ × Page))
    (hchain : schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂ \
        schedCache d C₀ σ t₂ ⊆ Q.image Prod.snd)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'')
    (hqinE : d t₂ ∈ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hnotE : ∀ s, t₂ < s → s ≤ t₂ + 1 + j →
      σ.getD s 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s)
    (P : Finset ℕ)
    (ht₂notP : t₂ ∉ P)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s) :
    schedCache (repairSchedule d t₂ (fifoSchedule σ C₀ t₂) (t₂ + 1 + j'')) C₀ σ (t₂ + 1 + j) =
      insert (d t₂) ((schedCache d C₀ σ (t₂ + 1 + j)).erase (fifoSchedule σ C₀ t₂)) := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  let q : Page := d t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule d t₂ q'' (t₂ + 1 + j'')
  have hft : σ.getD t₂ 0 ∉ schedCache e C₀ σ t₂ := by
    intro he
    exact (b2_ehit_ne σ ht₂ Q hpast hQ) (b2_ehit e d σ C₀ hftd (Q.image Prod.snd) hchain he)
  have hqq'' : q ≠ q'' := by
    intro hqq
    exact (first_disagree d σ C₀ hC₀ ht₂ hagree hdis).2.1 (by simpa [q, q'', hqq])
  have hsig_ne : σ.getD t₂ 0 ≠ q'' := by
    intro hsig
    exact hftd (hsig ▸ (by
      have hq''in : q'' ∈ schedCache d C₀ σ t₂ := by
        simpa [q''] using (first_disagree d σ C₀ hC₀ ht₂ hagree hdis).2.2
      exact hq''in))
  have hmain : ∀ s, t₂ + 1 ≤ s → s ≤ t₂ + 1 + j →
      schedCache r C₀ σ s = insert q ((schedCache d C₀ σ s).erase q'') := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hs_eq : s = t₂
        · -- base:s+1 = t₂+1
          subst s
          exact repairSchedule_base_swap d σ C₀ hC₀ ht₂ hagree hdis hqin rfl
            (show q = d t₂ from rfl) hj''
        · -- step:t₂ < s
          have hst : t₂ < s := by omega
          have hs1' : t₂ + 1 ≤ s := by omega
          have hs2' : s ≤ t₂ + 1 + j := by omega
          have hih := ih hs1' hs2'
          have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
          have hneq_q'' : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj'' (by omega) (by omega)
          have hds : r s = d s := by
            unfold r repairSchedule
            simp [show s ≠ t₂ by omega, show s ≠ t₂ + 1 + j'' by omega]
          rw [schedCache, schedCache]
          rw [hds]
          by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
          · -- r hits ⟹ d hits,双方 cache 不变,形式保持
            rw [if_pos hr]
            have hsigD : σ.getD s 0 ∈ schedCache d C₀ σ s := by
              rw [hih] at hr
              rcases Finset.mem_insert.mp hr with hqeq | hm
              · exfalso
                exact hneq_q hqeq
              · exact (Finset.mem_erase.mp hm).2
            rw [if_pos hsigD]
            rw [hih]
          · -- both fault
            have hsigD' : σ.getD s 0 ∉ schedCache d C₀ σ s := by
              intro h
              have hm : σ.getD s 0 ∈ insert q ((schedCache d C₀ σ s).erase q'') := by
                rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q'', h⟩)
              exact hr (hih ▸ hm)
            rw [if_neg hr]
            rw [if_neg hsigD']
            rw [hih]
            -- d s 的三种情形
            by_cases hds_q : d s = q
            · exfalso
              have hes_q : e s = q := by
                change exchangeSchedule d_pre t₀ q₀ q₀' σ C₀ s = q
                rw [← hd_eq s (hnot s (by omega) (by omega))]
                exact hds_q
              exact exchange_no_evict_q d_pre t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
                ht₂₀ ht₂₁ (show e t₂ = q from by
                  change exchangeSchedule d_pre t₀ q₀ q₀' σ C₀ t₂ = q
                  rw [← hd_eq t₂ ht₂notP]) hqinE hft hj (s := s) (by omega) (by omega)
                (hnotE s (by omega) (by omega)) hes_q
            · by_cases hds_q'' : d s = q''
              · -- d s = q'':双方的 erase 都是 no-op
                rw [hds_q'']
                rw [show (insert q ((schedCache d C₀ σ s).erase q'')).erase q'' =
                    insert q ((schedCache d C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hqq'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [show (insert (σ.getD s 0) ((schedCache d C₀ σ s).erase q'')).erase q'' =
                    insert (σ.getD s 0) ((schedCache d C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hneq_q'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [Finset.insert_comm]
              · -- d s ∉ {q, q''}:erase 交换,形式保持
                have hne_q : d s ≠ q := hds_q
                have hne_q'' : d s ≠ q'' := hds_q''
                rw [Finset.erase_insert_of_ne (a := q) (b := d s) (Ne.symm hne_q)]
                rw [Finset.erase_insert_of_ne (a := σ.getD s 0) (b := q'') hneq_q'']
                have herase_comm : ((schedCache d C₀ σ s).erase (d s)).erase q'' =
                    ((schedCache d C₀ σ s).erase q'').erase (d s) := by
                  ext x
                  simp [Finset.mem_erase, and_left_comm, and_assoc]
                rw [herase_comm]
                rw [Finset.insert_comm]
  exact hmain (t₂ + 1 + j) (by omega) le_rfl

/-- keep-swap 推导(当前调度 q'' 死版):`q''` 永不再请求的 B2 位置 `t₂` 处,
死页修复 `r = repairSchedule d t₂ q'' t₂` 的 swap 形式 `Ŝ = insert q (D − q'')`
在 `(t₂, J]` 上保持(尤其到 `J` —— 好事件,给出 `reverse_diff_chain_qp_dead`
的 `hkept`)。与 `repair_keep_swap_cur` 同构:`d s ≠ q` 由 `hd_eq`(off `P` 处
`d = e`)+ `hnot`(窗口内无过往修改位置)+ `exchange_no_evict_q` 给出;
`e` 于 `t₂` 缺页由 `b2_ehit` + `b2_ehit_ne` 从链 `hchain` 推出;
窗口内 `e` 缺页(`σ[s] ∉ E_s`)由 `hnotE` 给出。请求避开 `q''` 由 `hq''dead`
(`getD_ne_of_nextUse_none`,需要 `hJlen`)而非 `hj''` 给出,nop 由
`t₂ + 1 + j''` 换为 `t₂`(基例 `repairSchedule_base_swap_qp_dead`)。 -/
lemma repair_keep_swap_cur_qp_dead (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d_pre t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s →
      d_pre s ∈ schedCache d_pre C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d_pre C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : d t₂ ∈ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (d t₂) = some j)
    (hq''dead : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = none)
    (Q : Finset (ℕ × Page))
    (hchain : schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂ \
        schedCache d C₀ σ t₂ ⊆ Q.image Prod.snd)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'')
    (hqinE : d t₂ ∈ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hnotE : ∀ s, t₂ < s → s ≤ t₂ + 1 + j →
      σ.getD s 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s)
    (P : Finset ℕ)
    (ht₂notP : t₂ ∉ P)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s) :
    schedCache (repairSchedule d t₂ (fifoSchedule σ C₀ t₂) t₂) C₀ σ (t₂ + 1 + j) =
      insert (d t₂) ((schedCache d C₀ σ (t₂ + 1 + j)).erase (fifoSchedule σ C₀ t₂)) := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  let q : Page := d t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule d t₂ q'' t₂
  have hft : σ.getD t₂ 0 ∉ schedCache e C₀ σ t₂ := by
    intro he
    exact (b2_ehit_ne σ ht₂ Q hpast hQ) (b2_ehit e d σ C₀ hftd (Q.image Prod.snd) hchain he)
  have hqq'' : q ≠ q'' := by
    intro hqq
    exact (first_disagree d σ C₀ hC₀ ht₂ hagree hdis).2.1 (by simpa [q, q'', hqq])
  have hJlen : t₂ + 1 + j < σ.length := by
    have hjlt : j < (σ.drop (t₂ + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt
    omega
  have hmain : ∀ s, t₂ + 1 ≤ s → s ≤ t₂ + 1 + j →
      schedCache r C₀ σ s = insert q ((schedCache d C₀ σ s).erase q'') := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hs_eq : s = t₂
        · -- base:s+1 = t₂+1
          subst s
          exact repairSchedule_base_swap_qp_dead d σ C₀ hC₀ ht₂ hagree hdis hqin rfl
            (show q = d t₂ from rfl)
        · -- step:t₂ < s
          have hst : t₂ < s := by omega
          have hs1' : t₂ + 1 ≤ s := by omega
          have hs2' : s ≤ t₂ + 1 + j := by omega
          have hih := ih hs1' hs2'
          have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
          have hneq_q'' : σ.getD s 0 ≠ q'' := getD_ne_of_nextUse_none σ
            (by simpa [q''] using hq''dead) (by omega) (by omega)
          have hds : r s = d s := by
            unfold r repairSchedule
            simp [show s ≠ t₂ by omega]
          rw [schedCache, schedCache]
          rw [hds]
          by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
          · -- r hits ⟹ d hits,双方 cache 不变,形式保持
            rw [if_pos hr]
            have hsigD : σ.getD s 0 ∈ schedCache d C₀ σ s := by
              rw [hih] at hr
              rcases Finset.mem_insert.mp hr with hqeq | hm
              · exfalso
                exact hneq_q hqeq
              · exact (Finset.mem_erase.mp hm).2
            rw [if_pos hsigD]
            rw [hih]
          · -- both fault
            have hsigD' : σ.getD s 0 ∉ schedCache d C₀ σ s := by
              intro h
              have hm : σ.getD s 0 ∈ insert q ((schedCache d C₀ σ s).erase q'') := by
                rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q'', h⟩)
              exact hr (hih ▸ hm)
            rw [if_neg hr]
            rw [if_neg hsigD']
            rw [hih]
            -- d s 的三种情形
            by_cases hds_q : d s = q
            · exfalso
              have hes_q : e s = q := by
                change exchangeSchedule d_pre t₀ q₀ q₀' σ C₀ s = q
                rw [← hd_eq s (hnot s (by omega) (by omega))]
                exact hds_q
              exact exchange_no_evict_q d_pre t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
                ht₂₀ ht₂₁ (show e t₂ = q from by
                  change exchangeSchedule d_pre t₀ q₀ q₀' σ C₀ t₂ = q
                  rw [← hd_eq t₂ ht₂notP]) hqinE hft hj (s := s) (by omega) (by omega)
                (hnotE s (by omega) (by omega)) hes_q
            · by_cases hds_q'' : d s = q''
              · -- d s = q'':双方的 erase 都是 no-op
                rw [hds_q'']
                rw [show (insert q ((schedCache d C₀ σ s).erase q'')).erase q'' =
                    insert q ((schedCache d C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hqq'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [show (insert (σ.getD s 0) ((schedCache d C₀ σ s).erase q'')).erase q'' =
                    insert (σ.getD s 0) ((schedCache d C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hneq_q'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [Finset.insert_comm]
              · -- d s ∉ {q, q''}:erase 交换,形式保持
                have hne_q : d s ≠ q := hds_q
                have hne_q'' : d s ≠ q'' := hds_q''
                rw [Finset.erase_insert_of_ne (a := q) (b := d s) (Ne.symm hne_q)]
                rw [Finset.erase_insert_of_ne (a := σ.getD s 0) (b := q'') hneq_q'']
                have herase_comm : ((schedCache d C₀ σ s).erase (d s)).erase q'' =
                    ((schedCache d C₀ σ s).erase q'').erase (d s) := by
                  ext x
                  simp [Finset.mem_erase, and_left_comm, and_assoc]
                rw [herase_comm]
                rw [Finset.insert_comm]
  exact hmain (t₂ + 1 + j) (by omega) le_rfl

/-- B1 修复的 `q''` 缺席:`q''` 于 `t` 被修复逐出,在 `J''' = t + 1 + j'''`
之前不再回到修复的 cache(请求避开 `q''`,修复只插入 `σ[s]`)。
`swap_q_not_mem` 的修复版。 -/
lemma repair_q''_absent (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    {q'' : Page} (hq''in : q'' ∈ schedCache e C₀ σ t) (hq'' : q'' = fifoSchedule σ C₀ t)
    {j''' : ℕ} (hj''' : nextUse σ (t + 1) q'' = some j''') :
    ∀ s, t < s → s ≤ t + 1 + j''' →
      q'' ∉ schedCache (repairSchedule e t q'' (t + 1 + j''')) C₀ σ s := by
  let r : ℕ → Page := repairSchedule e t q'' (t + 1 + j''')
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs1 hs2
      by_cases hs_eq : s = t
      · subst s
        rw [schedCache]
        rw [schedCache_repairSchedule_eq_e e t q'' (t + 1 + j''') (by omega) σ C₀ le_rfl]
        rw [if_neg hft]
        rw [show repairSchedule e t q'' (t + 1 + j''') t = q'' by
          unfold repairSchedule
          simp]
        intro hm
        rw [Finset.mem_insert] at hm
        rcases hm with hqr | hqin2
        · exact hft (hqr ▸ hq''in)
        · exact (Finset.mem_erase.mp hqin2).1 rfl
      · have hts : t < s := by omega
        have hsJ : s < t + 1 + j''' := by omega
        have hsig_ne : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj''' (by omega) hsJ
        rw [schedCache]
        by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
        · rw [if_pos hr]
          exact ih hts (by omega)
        · rw [if_neg hr]
          intro hm
          rcases Finset.mem_insert.mp hm with hqr | hqin2
          · exact hsig_ne hqr.symm
          · exact ih hts (by omega) (Finset.mem_erase.mp hqin2).2

/-- B1 修复的 `J'''` 之后:反向差为空(`E − Ŝ = ∅`;超集方向由
`repairSchedule_superset` 给出)。基例 `J''' + 1`:`r` 于 `J'''` 缺页载入
`q''`(`hq''notS`,nop 逐出 `q''` 是 no-op),`e` 命中或载入 —— 两种情形下
`E − Ŝ ⊆ {q''}`(`hwin` 于 `J'''`)的残差 `q''` 都在 `Ŝ'` 中;归纳步
`r s = e s` 保持差为空(`e` 命中 ⟹ `r` 命中,其余情形逐元排除)。 -/
lemma repair_reverse_diff_after_nop (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hnoop : e t ∉ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t)
    {j''' : ℕ} (hj''' : nextUse σ (t + 1) q'' = some j''')
    (hq''notS : q'' ∉ schedCache (repairSchedule e t q'' (t + 1 + j''')) C₀ σ (t + 1 + j'''))
    (hwin : schedCache e C₀ σ (t + 1 + j''') \
        schedCache (repairSchedule e t q'' (t + 1 + j''')) C₀ σ (t + 1 + j''') ⊆
          ({q''} : Finset Page)) :
    ∀ s, t + 1 + j''' < s → s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j''')) C₀ σ s = ∅ := by
  let r : ℕ → Page := repairSchedule e t q'' (t + 1 + j''')
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let S : ℕ → Finset Page := schedCache r C₀ σ
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hsJ hslen
      by_cases hs_eq : s = t + 1 + j'''
      · subst s
        -- 基例:J'''+1,请求 q''
        change E (t + 1 + j''' + 1) \ S (t + 1 + j''' + 1) = ∅
        have hsig : σ.getD (t + 1 + j''') 0 = q'' := getD_eq_nextUse hj'''
        have hEcase : E (t + 1 + j''' + 1) =
            (if q'' ∈ E (t + 1 + j''') then E (t + 1 + j''')
             else insert q'' ((E (t + 1 + j''')).erase (e (t + 1 + j''')))) := by
          dsimp [E]
          rw [schedCache]
          rw [hsig]
        have hScase : S (t + 1 + j''' + 1) = insert q'' (S (t + 1 + j''')) := by
          dsimp [S]
          rw [schedCache]
          rw [hsig]
          rw [if_neg hq''notS]
          rw [show r (t + 1 + j''') = q'' by unfold r repairSchedule; simp]
          rw [Finset.erase_eq_of_notMem hq''notS]
        by_cases he : q'' ∈ E (t + 1 + j''')
        · -- e 命中:cache 不变
          rw [hEcase, if_pos he]
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          rw [Finset.mem_sdiff] at hx
          by_cases hxq : x = q''
          · exact hx.2 (by rw [hScase]; rw [hxq]; exact Finset.mem_insert_self _ _)
          · have hmem : x ∈ E (t + 1 + j''') \ S (t + 1 + j''') := by
              rw [Finset.mem_sdiff]
              exact ⟨hx.1, by
                intro hxS
                exact hx.2 (by rw [hScase]; exact Finset.mem_insert.mpr (Or.inr hxS))⟩
            have hxq' := Finset.mem_singleton.mp (hwin hmem)
            exact hxq hxq'
        · -- e 缺页:载入 q''
          rw [hEcase, if_neg he]
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          rw [Finset.mem_sdiff] at hx
          by_cases hxq : x = q''
          · exact hx.2 (by rw [hScase]; rw [hxq]; exact Finset.mem_insert_self _ _)
          · have hmem : x ∈ E (t + 1 + j''') \ S (t + 1 + j''') := by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hxq hxp
                · exact (Finset.mem_erase.mp hxE2).2, by
                intro hxS
                exact hx.2 (by rw [hScase]; exact Finset.mem_insert.mpr (Or.inr hxS))⟩
            have hxq' := Finset.mem_singleton.mp (hwin hmem)
            exact hxq hxq'
      · -- 归纳步:J''' < s
        have hsJ' : t + 1 + j''' < s := by omega
        have hih := ih hsJ' (by omega)
        have hs_ne_t : s ≠ t := by omega
        have hs_ne_J''' : s ≠ t + 1 + j''' := by omega
        have hrs : r s = e s := by
          unfold r repairSchedule
          simp [hs_ne_t, hs_ne_J''']
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [schedCache, schedCache] at hx
        rw [show (repairSchedule e t q'' (t + 1 + j''')) s = e s by exact hrs] at hx
        by_cases he : σ.getD s 0 ∈ E s
        · -- e 命中 ⟹ r 命中(E − Ŝ = ∅)
          rw [if_pos he] at hx
          have hr' : σ.getD s 0 ∈ S s := by
            by_contra hnot
            exact (Finset.notMem_empty (σ.getD s 0)) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨he, hnot⟩))
          rw [if_pos hr'] at hx
          exact (Finset.notMem_empty x) (hih ▸ (by
            rw [Finset.mem_sdiff]
            exact ⟨hx.1, hx.2⟩))
        · -- e 缺页
          rw [if_neg he] at hx
          by_cases hr' : σ.getD s 0 ∈ S s
          · -- r 命中:Ŝ 不变,E 载入
            rw [if_pos hr'] at hx
            exact (Finset.notMem_empty x) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hx.2 (hxp.symm ▸ hr')
                · exact (Finset.mem_erase.mp hxE2).2, hx.2⟩))
          · -- 双缺页
            rw [if_neg hr'] at hx
            exact (Finset.notMem_empty x) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hx.2 (Finset.mem_insert.mpr (Or.inl hxp))
                · exact (Finset.mem_erase.mp hxE2).2, by
                  intro hxS
                  by_cases hxeq : x = σ.getD s 0
                  · exfalso
                    exact hx.2 (Finset.mem_insert.mpr (Or.inl hxeq))
                  · rcases Finset.mem_insert.mp hx.1 with hxp | hxE2'
                    · exfalso
                      exact hxeq hxp
                    · exact hx.2 (Finset.mem_insert.mpr
                        (Or.inr (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxE2').1, hxS⟩)))⟩))

/-- 分支分析:交换在 `t` 之后(窗口内)的缺页处,逐出 `e s` 是 `q'` 或
resident(`e s ∈ E_s ∪ {q'}`)。`exchangeDecision` 的结构:分支 1 逐出
`q'`;分支 4-6 逐出 `E − D` 中的页或 `d s ∈ E_s`;`M` 空时的 `else 0`
由缺页 + 基数论证(`exchangeScheduleCore_card`)排除。这是 `hqinE`(B2 处
`q ∈ E_{t₂}` —— `q'` 枝是 B1)与 "交换从不逐出过往 `q''ᵢ`" 的机制。 -/
lemma exchange_evict_mem_or_q' (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hs1 : t < s)
    (hFault : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) :
    (exchangeSchedule d t q q' σ C₀) s = q' ∨
      (exchangeSchedule d t q q' σ C₀) s ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  change (exchangeScheduleCore d t q q' σ C₀ s).2 = q' ∨
    (exchangeScheduleCore d t q q' σ C₀ s).2 ∈ schedCache e C₀ σ s
  rw [exchangeScheduleCore_second]
  rw [← schedCache_exchangeScheduleCore]
  change exchangeDecision d t q q' σ C₀ (schedCache e C₀ σ s) s = q' ∨
    exchangeDecision d t q q' σ C₀ (schedCache e C₀ σ s) s ∈ schedCache e C₀ σ s
  unfold exchangeDecision
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  by_cases h1 : d s = q'
  · rw [if_pos h1]
    exact Or.inl rfl
  · rw [if_neg h1]
    by_cases hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧ σ.getD s 0 ∈ schedCache d C₀ σ s
    · rw [if_pos hb4]
      let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
      by_cases hf : (M.filter (fun x => x ≠ q')).Nonempty
      · rw [dif_pos hf]
        exact Or.inr ((Finset.mem_sdiff.mp (Finset.mem_filter.mp (Classical.choose_spec hf)).1).1)
      · by_cases hm : M.Nonempty
        · rw [dif_neg hf]
          rw [dif_pos hm]
          exact Or.inr ((Finset.mem_sdiff.mp (Classical.choose_spec hm)).1)
        · rw [dif_neg hf]
          rw [dif_neg hm]
          exfalso
          have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
            rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t q q' σ C₀ s).1 by
              rw [← schedCache_exchangeScheduleCore]]
            exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
          have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          exact hFault (hEq.symm ▸ hb4.2)
    · rw [if_neg hb4]
      by_cases hdsin : d s ∈ schedCache e C₀ σ s
      · rw [if_pos hdsin]
        exact Or.inr hdsin
      · rw [if_neg hdsin]
        let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
        by_cases hm : M.Nonempty
        · rw [dif_pos hm]
          exact Or.inr ((Finset.mem_sdiff.mp (Classical.choose_spec hm)).1)
        · rw [dif_neg hm]
          exfalso
          have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
            rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t q q' σ C₀ s).1 by
              rw [← schedCache_exchangeScheduleCore]]
            exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
          have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          have hdFault : σ.getD s 0 ∉ schedCache d C₀ σ s := by
            intro h
            exact hFault (hEq.symm ▸ h)
          have hdsE : d s ∈ schedCache d C₀ σ s := hweak s (by omega) hdFault
          exact hdsin (hEq.symm ▸ hdsE)

/-- no-nop-at-B2 推导(最后修复分析的核心):`P` 是过往修复位置集
(`tᵢ` 与活对的 nop `tᵢ + 1 + j''ᵢ`),`hcomp` 是值不变式 —— 每个 `P`
位置的值是某对的页(`s = tᵢ` 或 `s = nᵢ` 且 `d s = q''`),`hpair` 给出
每对在其 `tᵢ` 处的过往事实(`σ[tᵢ]` 缺页、`q''` resident、`d tᵢ = q''`,
修复后保持)。B2 位置 `t`(`d t ∈ D_t`)处:若 `t ∈ P`,则 `t = tᵢ`
(`hpast` 矛盾)或 `t = nᵢ` —— 值不变式给 `d t = q''`,而
`evicted_page_absent_until_request`(逐出后未请求)给 `q'' ∉ D_t`,
与 `d t ∈ D_t` 矛盾。 -/
lemma no_nop_at_b2 (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    {t : ℕ}
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t)
    (hP : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j''))
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q''))
    (hpair : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = some j'' →
      σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧
      q'' ∈ schedCache d C₀ σ tᵢ ∧
      d tᵢ = q'')
    (ht : t < σ.length)
    (hqin : d t ∈ schedCache d C₀ σ t) :
    t ∉ P := by
  intro htP
  rcases hP t htP with ⟨tᵢ, q'', htq, hteq⟩ | ⟨tᵢ, q'', j'', htq, hnext, hteq⟩
  · -- t = tᵢ:tᵢ < t 矛盾
    have hlt : tᵢ < t := hpast tᵢ q'' htq
    omega
  · -- t = nᵢ:值不变式给 d t = q''(某对),而 q'' ∉ D_t(逐出后未请求)
    rcases hcomp t htP with hc1 | hc2
    · -- t 也是某对的 tᵢ:hpast 矛盾
      rcases hc1 with ⟨tₗ, qₗ, htqₗ, hteqₗ, hdtₗ⟩
      have hlt : tₗ < t := hpast tₗ qₗ htqₗ
      omega
    · -- t = nₗ 且 d t = qₗ:evicted_page_absent_until_request
      rcases hc2 with ⟨tₗ, qₗ, jₗ, htqₗ, hnextₗ, hteqₗ, hdtₗ⟩
      rcases hpair tₗ qₗ jₗ htqₗ hnextₗ with ⟨hftₗ, hqresₗ, hdtₗ'⟩
      have habs : qₗ ∉ schedCache d C₀ σ (tₗ + 1 + jₗ) :=
        evicted_page_absent_until_request d σ C₀ tₗ qₗ hftₗ hqresₗ hdtₗ' hnextₗ
      have : qₗ ∉ schedCache d C₀ σ t := by
        rwa [hteqₗ]
      exact this (hdtₗ ▸ hqin)

/- ### 情形步的扩展胶水(hpast/hQfifo/hP/hP_in/hcomp/hpair)

情形 B1/B2 步的新状态带 `Q' = insert (t₂, q'') Q` 与
`P' = P ∪ {t₂, nop}`(活对 nop = `t₂ + 1 + j''`;死页修复 nop = `t₂`,即
`P' = P ∪ {t₂}`)。以下扩展引理把旧状态的组成不变式族(见 `IterateState`)
传到新状态:旧位置由旧不变式(`r` 与 `d` 在 `{t₂, nop}` 之外一致、cache 在
`tᵢ ≤ t₂` 处一致),新位置/新对由情形步本身的事实(`r t₂ = q''`、
`r nop = q''`、`σ[t₂]` 缺页、`q''` resident)见证。hQ 的扩展是遗留障碍
(见 DESIGN:`t₂ + 1 < J''ᵢ` 的严格界对旧对在全历史 Q 上不成立)。 -/

/-- hpast 扩展:新对 `(t₂, q'')` 加入 Q 后,所有对的修复位置 `tᵢ` 严格在新
界 `t₂ + 1` 之前(旧对由 `hpast`,新对 `t₂ < t₂ + 1`)。 -/
lemma extend_hpast (Q : Finset (ℕ × Page)) {t₂ : ℕ} {q'' : Page}
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂) :
    ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q → tᵢ < t₂ + 1 := by
  intro tᵢ q''₀ htq
  rw [Finset.mem_insert] at htq
  rcases htq with hEq | htq
  · rcases hEq with ⟨rfl, rfl⟩
    omega
  · have hlt : tᵢ < t₂ := hpast tᵢ q''₀ htq
    omega

/-- hQfifo 扩展:新对 `(t₂, q'')` 的页正是 FIF 在 `t₂` 的逐出页(`hq''`),
旧对由 `hQfifo`。 -/
lemma extend_hQfifo (σ : List Page) (C₀ : Finset Page) (Q : Finset (ℕ × Page))
    {t₂ : ℕ} {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t₂)
    (hQfifo : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = fifoSchedule σ C₀ tᵢ) :
    ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q → q''₀ = fifoSchedule σ C₀ tᵢ := by
  intro tᵢ q''₀ htq
  rw [Finset.mem_insert] at htq
  rcases htq with hEq | htq
  · rcases hEq with ⟨rfl, rfl⟩
    exact hq''
  · exact hQfifo tᵢ q''₀ htq

/-- hP 扩展(活对版):`P' = P ∪ {t₂, t₂+1+j''}`。旧位置沿用旧 `hP`(见证对
仍在 `Q'` 中),新位置 `t₂` 与新 nop `J'' = t₂+1+j''` 由新对 `(t₂, q'')`
见证(`s = tᵢ` 与 `s = tᵢ+1+j''`)。 -/
lemma extend_hP (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ) {t₂ : ℕ} {q'' : Page}
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) q'' = some j'')
    (hP : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀)) :
    ∀ s, s ∈ P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) := by
  intro s hs
  rw [Finset.mem_union] at hs
  rcases hs with hsP | hsNew
  · rcases hP s hsP with h1 | h2
    · rcases h1 with ⟨tᵢ, q''₀, htq, hteq⟩
      left
      refine ⟨tᵢ, q''₀, ?_, hteq⟩
      exact Finset.mem_insert.mpr (Or.inr htq)
    · rcases h2 with ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq⟩
      right
      refine ⟨tᵢ, q''₀, j''₀, ?_, hnext₀, hteq⟩
      exact Finset.mem_insert.mpr (Or.inr htq)
  · rw [Finset.mem_insert] at hsNew
    rcases hsNew with hEq | hsNew
    · left
      exact ⟨t₂, q'', Finset.mem_insert_self _ _, hEq⟩
    · right
      refine ⟨t₂, q'', j'', Finset.mem_insert_self _ _, hj'', ?_⟩
      exact Finset.mem_singleton.mp hsNew

/-- hP 的反向(活对版):新/旧对见证的位置都在 `P ∪ {t₂, J''}` 中。新对
`(t₂, q'')` 的 nop 见证的 `j''₀` 由 nextUse 唯一性等于 `j''`;`hpast` 排除
`(t₂, q''₀) ∈ Q`(旧对位置 `tᵢ ≠ t₂`)。 -/
lemma extend_hP_in (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ) {t₂ : ℕ} {q'' : Page}
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) q'' = some j'')
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hP_in : ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) → s ∈ P) :
    ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) → s ∈ P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) := by
  intro s hw
  rcases hw with ⟨tᵢ, q''₀, htq, hteq⟩ | ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq⟩
  · by_cases ht₂ : tᵢ = t₂
    · rw [ht₂] at hteq
      rw [Finset.mem_union]
      right
      rw [Finset.mem_insert]
      exact Or.inl hteq
    · rw [Finset.mem_union]
      left
      exact hP_in s (Or.inl ⟨tᵢ, q''₀, by
        rw [Finset.mem_insert] at htq
        rcases htq with hEq | htq'
        · rcases hEq with ⟨rfl, rfl⟩
          exfalso
          exact ht₂ rfl
        · exact htq', hteq⟩)
  · by_cases ht₂ : tᵢ = t₂
    · have hqeq : q''₀ = q'' := by
        rw [Finset.mem_insert] at htq
        rcases htq with hEq | htq'
        · rcases hEq with ⟨rfl, rfl⟩
          rfl
        · exfalso
          rw [ht₂] at htq'
          exact (Nat.lt_irrefl t₂) (hpast t₂ q''₀ htq')
      have hnext₀' : nextUse σ (t₂ + 1) q''₀ = some j''₀ := by
        rwa [ht₂] at hnext₀
      have hj''₀ : j''₀ = j'' := Option.some.inj (hnext₀'.symm.trans (by simpa [hqeq.symm] using hj''))
      rw [Finset.mem_union]
      right
      rw [Finset.mem_insert]
      right
      rw [Finset.mem_singleton]
      omega
    · rw [Finset.mem_union]
      left
      exact hP_in s (Or.inr ⟨tᵢ, q''₀, j''₀, by
        rw [Finset.mem_insert] at htq
        rcases htq with hEq | htq'
        · rcases hEq with ⟨rfl, rfl⟩
          exfalso
          exact ht₂ rfl
        · exact htq', hnext₀, hteq⟩)

/-- hcomp 扩展(活对版):新调度 `r` 在 `P' = P ∪ {t₂, J''}` 上的值不变式。
旧位置(≠ 新 nop)沿用旧 `hcomp`(`r s = d s`);`t₂` 与新 nop 由新对
`(t₂, q'')` 见证(`r` 于 `t₂`、`J''` 逐出 `q''` —— 新 nop 覆盖旧位置时新见证
依然成立)。 -/
lemma extend_hcomp (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (r d : ℕ → Page) {t₂ : ℕ} {q'' : Page}
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) q'' = some j'')
    (hrt : r t₂ = q'') (hrN : r (t₂ + 1 + j'') = q'')
    (hre : ∀ s, s ∉ ({t₂, t₂ + 1 + j''} : Finset ℕ) → r s = d s)
    (ht₂notP : t₂ ∉ P)
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q ∧ s = tᵢ ∧ d s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ d s = q''₀)) :
    ∀ s, s ∈ P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧ s = tᵢ ∧ r s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ r s = q''₀) := by
  intro s hs
  rw [Finset.mem_union] at hs
  rcases hs with hsP | hsNew
  · by_cases hsN : s = t₂ + 1 + j''
    · subst s
      right
      refine ⟨t₂, q'', j'', Finset.mem_insert_self _ _, hj'', rfl, hrN⟩
    · rcases hcomp s hsP with h1 | h2
      · rcases h1 with ⟨tᵢ, q''₀, htq, hteq, hds⟩
        left
        refine ⟨tᵢ, q''₀, ?_, hteq, ?_⟩
        · exact Finset.mem_insert.mpr (Or.inr htq)
        · have hsne : s ≠ t₂ := by
            intro hst
            exact ht₂notP (hst ▸ hsP)
          rw [hre s (by
            intro hmem
            rw [Finset.mem_insert] at hmem
            rcases hmem with hEq | hmem
            · exact hsne hEq
            · exact hsN (Finset.mem_singleton.mp hmem))]
          exact hds
      · rcases h2 with ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq, hds⟩
        right
        refine ⟨tᵢ, q''₀, j''₀, ?_, hnext₀, hteq, ?_⟩
        · exact Finset.mem_insert.mpr (Or.inr htq)
        · have hsne : s ≠ t₂ := by
            intro hst
            exact ht₂notP (hst ▸ hsP)
          rw [hre s (by
            intro hmem
            rw [Finset.mem_insert] at hmem
            rcases hmem with hEq | hmem
            · exact hsne hEq
            · exact hsN (Finset.mem_singleton.mp hmem))]
          exact hds
  · rw [Finset.mem_insert] at hsNew
    rcases hsNew with hEq | hsNew
    · subst s
      left
      refine ⟨t₂, q'', Finset.mem_insert_self _ _, rfl, hrt⟩
    · rw [Finset.mem_singleton] at hsNew
      subst s
      right
      refine ⟨t₂, q'', j'', Finset.mem_insert_self _ _, hj'', rfl, hrN⟩

/-- hpair 扩展:新对 `(t₂, q'')` 的过往事实(`σ[t₂]` 缺页、`q''` resident、
`r t₂ = q''`)与旧对的(`r` 的 cache 在 `tᵢ ≤ t₂` 与 `d` 一致、`r tᵢ = d tᵢ`,
由 `hpair` 传递)。 -/
lemma extend_hpair (σ : List Page) (C₀ : Finset Page) (Q : Finset (ℕ × Page))
    (r d : ℕ → Page) {t₂ : ℕ} {q'' : Page}
    (hft : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    (hq''in : q'' ∈ schedCache d C₀ σ t₂)
    (hrt : r t₂ = q'')
    (hre : ∀ s, s ≠ t₂ → r s = d s)
    (hce : ∀ s, s ≤ t₂ → schedCache r C₀ σ s = schedCache d C₀ σ s)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hpair : ∀ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q →
      nextUse σ (tᵢ + 1) q''₀ = some j''₀ →
      σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧ q''₀ ∈ schedCache d C₀ σ tᵢ ∧ d tᵢ = q''₀) :
    ∀ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q →
      nextUse σ (tᵢ + 1) q''₀ = some j''₀ →
      σ.getD tᵢ 0 ∉ schedCache r C₀ σ tᵢ ∧ q''₀ ∈ schedCache r C₀ σ tᵢ ∧ r tᵢ = q''₀ := by
  intro tᵢ q''₀ j''₀ htq hnext
  rw [Finset.mem_insert] at htq
  rcases htq with hEq | htq
  · rcases hEq with ⟨rfl, rfl⟩
    constructor
    · rw [hce t₂ le_rfl]
      exact hft
    constructor
    · rw [hce t₂ le_rfl]
      exact hq''in
    · exact hrt
  · have htᵢlt : tᵢ < t₂ := hpast tᵢ q''₀ htq
    rcases hpair tᵢ q''₀ j''₀ htq hnext with ⟨hftᵢ, hqinᵢ, hdtᵢ⟩
    constructor
    · rw [hce tᵢ (by omega)]
      exact hftᵢ
    constructor
    · rw [hce tᵢ (by omega)]
      exact hqinᵢ
    · rw [hre tᵢ (by omega)]
      exact hdtᵢ

/-- hP 扩展(死页版):`P' = P ∪ {t₂}`(死页修复没有 nop 位置)。 -/
lemma extend_hP_dead (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    {t₂ : ℕ} {q'' : Page}
    (hP : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀)) :
    ∀ s, s ∈ P ∪ ({t₂} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) := by
  intro s hs
  rw [Finset.mem_union] at hs
  rcases hs with hsP | hsNew
  · rcases hP s hsP with h1 | h2
    · rcases h1 with ⟨tᵢ, q''₀, htq, hteq⟩
      left
      refine ⟨tᵢ, q''₀, ?_, hteq⟩
      exact Finset.mem_insert.mpr (Or.inr htq)
    · rcases h2 with ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq⟩
      right
      refine ⟨tᵢ, q''₀, j''₀, ?_, hnext₀, hteq⟩
      exact Finset.mem_insert.mpr (Or.inr htq)
  · rw [Finset.mem_singleton] at hsNew
    subst s
    left
    exact ⟨t₂, q'', Finset.mem_insert_self _ _, rfl⟩

/-- hP 反向(死页版):新对 `(t₂, q'')` 死页(`nextUse = none`),其 nop 见证
不可能,只有 `s = t₂` 见证。 -/
lemma extend_hP_in_dead (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    {t₂ : ℕ} {q'' : Page}
    (hq''dead : nextUse σ (t₂ + 1) q'' = none)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hP_in : ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) → s ∈ P) :
    ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) → s ∈ P ∪ ({t₂} : Finset ℕ) := by
  intro s hw
  rcases hw with ⟨tᵢ, q''₀, htq, hteq⟩ | ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq⟩
  · by_cases ht₂ : tᵢ = t₂
    · rw [ht₂] at hteq
      rw [Finset.mem_union]
      right
      rw [Finset.mem_singleton]
      exact hteq
    · rw [Finset.mem_union]
      left
      exact hP_in s (Or.inl ⟨tᵢ, q''₀, by
        rw [Finset.mem_insert] at htq
        rcases htq with hEq | htq'
        · rcases hEq with ⟨rfl, rfl⟩
          exfalso
          exact ht₂ rfl
        · exact htq', hteq⟩)
  · by_cases ht₂ : tᵢ = t₂
    · have hqeq : q''₀ = q'' := by
        rw [Finset.mem_insert] at htq
        rcases htq with hEq | htq'
        · rcases hEq with ⟨rfl, rfl⟩
          rfl
        · exfalso
          rw [ht₂] at htq'
          exact (Nat.lt_irrefl t₂) (hpast t₂ q''₀ htq')
      exfalso
      rw [ht₂] at hnext₀
      rw [hqeq] at hnext₀
      rw [hq''dead] at hnext₀
      cases hnext₀
    · rw [Finset.mem_union]
      left
      exact hP_in s (Or.inr ⟨tᵢ, q''₀, j''₀, by
        rw [Finset.mem_insert] at htq
        rcases htq with hEq | htq'
        · rcases hEq with ⟨rfl, rfl⟩
          exfalso
          exact ht₂ rfl
        · exact htq', hnext₀, hteq⟩)

/-- hcomp 扩展(死页版):`P' = P ∪ {t₂}`;`t₂` 由新对见证(`r t₂ = q''`),
旧位置 `r s = d s` 沿用旧 `hcomp`。 -/
lemma extend_hcomp_dead (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (r d : ℕ → Page) {t₂ : ℕ} {q'' : Page}
    (hrt : r t₂ = q'')
    (hre : ∀ s, s ≠ t₂ → r s = d s)
    (ht₂notP : t₂ ∉ P)
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q ∧ s = tᵢ ∧ d s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ d s = q''₀)) :
    ∀ s, s ∈ P ∪ ({t₂} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧ s = tᵢ ∧ r s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ r s = q''₀) := by
  intro s hs
  rw [Finset.mem_union] at hs
  rcases hs with hsP | hsNew
  · rcases hcomp s hsP with h1 | h2
    · rcases h1 with ⟨tᵢ, q''₀, htq, hteq, hds⟩
      left
      refine ⟨tᵢ, q''₀, ?_, hteq, ?_⟩
      · exact Finset.mem_insert.mpr (Or.inr htq)
      · have hsne : s ≠ t₂ := by
          intro hst
          exact ht₂notP (hst ▸ hsP)
        rw [hre s hsne]
        exact hds
    · rcases h2 with ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq, hds⟩
      right
      refine ⟨tᵢ, q''₀, j''₀, ?_, hnext₀, hteq, ?_⟩
      · exact Finset.mem_insert.mpr (Or.inr htq)
      · have hsne : s ≠ t₂ := by
          intro hst
          exact ht₂notP (hst ▸ hsP)
        rw [hre s hsne]
        exact hds
  · rw [Finset.mem_singleton] at hsNew
    subst s
    left
    refine ⟨t₂, q'', Finset.mem_insert_self _ _, rfl, hrt⟩

/-- 迭代的情形 B1(活子情形):窗口内 no-op 分歧 `t₂`(`d t₂ ∉ cache`)处,
`q''` 会再次被请求(`hj'''`)时,修复 `r = repairSchedule d t₂ q'' (t₂ + 1 + j''')`
满足:一致到 `t₂ + 1`(`repair_step`);miss 记账精确 —— `rF ≤ eF` 处处,
`J'''` 处 `rF = 1` 而 `eF = 1 − bad`(坏事件 `bad = σ[J'''] ∈ D_{J'''}`),
故 `schedMisses r ≤ schedMisses d + bad`(slack 记账 `slack − bad`);
反向差链扩展 `insert q'' (Q.image Prod.snd)`(`repair_diff_noop_window` +
`repair_reverse_diff_after_nop`,后者由 `repairSchedule_superset` 补超集
方向);`hd_eq` 扩展到 `P ∪ {t₂, J'''}`;reduced 界 `max hnb (J''' + 1)`
(`repairSchedule_superset`)。 -/
lemma iterate_main_case_b1_alive (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length)
    (hnb : ℕ) (ht₂hnb : t₂ < hnb)
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : d t₂ ∉ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''')
    (Q : Finset (ℕ × Page))
    (hchain : ∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
        schedCache d C₀ σ s ⊆ Q.image Prod.snd)
    (P : Finset ℕ)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hdred : ∀ s, hnb ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s →
      d s ∈ schedCache d C₀ σ s) :
    ∃ r : ℕ → Page,
      agreeWithFIF r C₀ σ (t₂ + 1) ∧
      schedMisses r C₀ σ ≤ schedMisses d C₀ σ +
        (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''') then 1 else 0) ∧
      (∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
          schedCache r C₀ σ s ⊆ insert (fifoSchedule σ C₀ t₂) (Q.image Prod.snd)) ∧
      (∀ s, s ∉ P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
        r s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s) ∧
      (∀ s, max hnb (t₂ + 1 + j''' + 1) ≤ s →
        σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s) := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule d t₂ q'' (t₂ + 1 + j''')
  have hq''res : q'' ∈ schedCache d C₀ σ t₂ := by
    have hfd := first_disagree d σ C₀ hC₀ ht₂ hagree hdis
    simpa [q''] using hfd.2.2
  have hq''notS : ∀ s, t₂ < s → s ≤ t₂ + 1 + j''' → q'' ∉ schedCache r C₀ σ s := by
    intro s hs1 hs2
    exact repair_q''_absent d σ C₀ hftd hq''res rfl hj''' s hs1 hs2
  have hwindow := repair_diff_noop_window d σ C₀ hnoop hftd rfl hj'''
  have hafter : ∀ s, t₂ + 1 + j''' < s → s ≤ σ.length →
      schedCache d C₀ σ s \ schedCache r C₀ σ s = ∅ := by
    intro s hs1 hs2
    exact repair_reverse_diff_after_nop d σ C₀ hnoop hftd rfl hj'''
      (hq''notS (t₂ + 1 + j''') (by omega) le_rfl) (hwindow (t₂ + 1 + j''') le_rfl).1 s hs1 hs2
  have hce : ∀ s, s ≤ t₂ → schedCache r C₀ σ s = schedCache d C₀ σ s := by
    intro s hs
    exact schedCache_repairSchedule_eq_e d t₂ q'' (t₂ + 1 + j''') (by omega) σ C₀ hs
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · -- agree 到 t₂+1
    exact (repair_step d σ C₀ hC₀ ht₂ hagree hdis hnoop hj''').2
  · -- miss 记账:schedMisses r ≤ schedMisses d + bad
    have hpoint_le : ∀ s, s < σ.length → s ≠ t₂ + 1 + j''' →
        schedFaultAt r C₀ σ s ≤ schedFaultAt d C₀ σ s := by
      intro s hs hsne
      unfold schedFaultAt
      by_cases hs_le_t : s ≤ t₂
      · -- caches equal
        rw [hce s hs_le_t]
      · by_cases hsJ : s ≤ t₂ + 1 + j'''
        · -- t₂ < s < J''':hit/fault 对齐(窗口差)
          have hst : t₂ < s := by omega
          have hsJ' : s < t₂ + 1 + j''' := by omega
          have hneq_q'' : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj''' (by omega) (by omega)
          by_cases he : σ.getD s 0 ∈ schedCache d C₀ σ s
          · rw [if_pos he]
            rw [if_pos (by
              by_contra hr
              have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨he, hr⟩
              exact hneq_q'' (Finset.mem_singleton.mp ((hwindow s (by omega)).1 hmem)))]
          · rw [if_neg he]
            rw [if_neg (by
              intro hr
              exact he ((hwindow s (by omega)).2 hr))]
        · -- s > J''':D − Ŝ = ∅ ⟹ e 命中 ⟹ r 命中
          have hsJ' : t₂ + 1 + j''' < s := by omega
          by_cases he : σ.getD s 0 ∈ schedCache d C₀ σ s
          · rw [if_pos he]
            rw [if_pos (by
              by_contra hr
              have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨he, hr⟩
              exact (Finset.notMem_empty (σ.getD s 0)) ((hafter s hsJ' (by omega)) ▸ hmem))]
          · rw [if_neg he]
            by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
            · rw [if_pos hr]
              omega
            · rw [if_neg hr]
    have hpoint : ∀ s, s < σ.length → schedFaultAt r C₀ σ s ≤
        schedFaultAt d C₀ σ s +
          (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''') then 1 else 0) := by
      intro s hs
      by_cases hs_eq : s = t₂ + 1 + j'''
      · subst s
        unfold schedFaultAt
        rw [show σ.getD (t₂ + 1 + j''') 0 = q'' by exact getD_eq_nextUse hj''']
        rw [if_neg (hq''notS (t₂ + 1 + j''') (by omega) le_rfl)]
        by_cases hb : q'' ∈ schedCache d C₀ σ (t₂ + 1 + j''')
        · simp [hb]
        · simp [hb]
      · exact le_trans (hpoint_le s hs hs_eq) (Nat.le_add_right _ _)
    unfold schedMisses
    change (∑ s ∈ Finset.range σ.length, schedFaultAt r C₀ σ s) ≤
      (∑ s ∈ Finset.range σ.length, schedFaultAt d C₀ σ s) +
        (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''') then 1 else 0)
    have hsig : σ.getD (t₂ + 1 + j''') 0 = q'' := getD_eq_nextUse hj'''
    have hrFJ : schedFaultAt r C₀ σ (t₂ + 1 + j''') = 1 := by
      unfold schedFaultAt
      rw [hsig]
      rw [if_neg (hq''notS (t₂ + 1 + j''') (by omega) le_rfl)]
    have hJin : t₂ + 1 + j''' ∈ Finset.range σ.length := by
      rw [Finset.mem_range]
      have hjlt : j''' < (σ.drop (t₂ + 1)).length := (nextUse_eq_some_iff.mp hj''').1
      rw [List.length_drop] at hjlt
      omega
    have hsum_erase_r : (∑ s ∈ (Finset.range σ.length).erase (t₂ + 1 + j'''),
          schedFaultAt r C₀ σ s) + 1 = ∑ s ∈ Finset.range σ.length, schedFaultAt r C₀ σ s := by
      rw [← Finset.sum_erase_add (s := Finset.range σ.length) (a := t₂ + 1 + j''')
        (f := schedFaultAt r C₀ σ) hJin]
      rw [hrFJ]
    have hsum_erase_d : (∑ s ∈ (Finset.range σ.length).erase (t₂ + 1 + j'''),
          schedFaultAt d C₀ σ s) + schedFaultAt d C₀ σ (t₂ + 1 + j''') =
        ∑ s ∈ Finset.range σ.length, schedFaultAt d C₀ σ s := by
      exact Finset.sum_erase_add (s := Finset.range σ.length) (a := t₂ + 1 + j''')
        (f := schedFaultAt d C₀ σ) hJin
    have hsum_le : (∑ s ∈ (Finset.range σ.length).erase (t₂ + 1 + j'''),
          schedFaultAt r C₀ σ s) ≤
        ∑ s ∈ (Finset.range σ.length).erase (t₂ + 1 + j'''), schedFaultAt d C₀ σ s := by
      exact Finset.sum_le_sum (fun s hs => hpoint_le s (by
        exact Finset.mem_range.mp (Finset.mem_erase.mp hs).2) (Finset.mem_erase.mp hs).1)
    by_cases hbad : σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''')
    · -- 坏事件:Σ rF ≤ Σ eF + 1
      rw [if_pos hbad]
      have heFJ : schedFaultAt d C₀ σ (t₂ + 1 + j''') = 0 := by
        unfold schedFaultAt
        rw [hsig]
        rw [if_pos (by rwa [← hsig])]
      rw [← hsum_erase_r]
      have h' := hsum_erase_d
      rw [heFJ] at h'
      omega
    · -- 非坏事件:Σ rF ≤ Σ eF(J''' 处 rF = eF = 1)
      rw [if_neg hbad]
      have heFJ : schedFaultAt d C₀ σ (t₂ + 1 + j''') = 1 := by
        unfold schedFaultAt
        rw [hsig]
        rw [if_neg (by rwa [← hsig])]
      rw [← hsum_erase_r]
      have h' := hsum_erase_d
      rw [heFJ] at h'
      omega
  · -- 链扩展到 insert q'' (Q.image Prod.snd)
    intro s hslen
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hsJ : s ≤ t₂ + 1 + j'''
    · by_cases hxD : x ∈ schedCache d C₀ σ s
      · have hmem : x ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
          rw [Finset.mem_sdiff]
          exact ⟨hxD, hx.2⟩
        rw [Finset.mem_insert]
        exact Or.inl (Finset.mem_singleton.mp ((hwindow s hsJ).1 hmem))
      · rw [Finset.mem_insert]
        exact Or.inr (hchain s hslen (by
          rw [Finset.mem_sdiff]
          exact ⟨hx.1, hxD⟩))
    · -- s > J''':D − Ŝ = ∅;x ∈ D 矛盾,x ∉ D 走链
      have hsJ' : t₂ + 1 + j''' < s := by omega
      by_cases hxD : x ∈ schedCache d C₀ σ s
      · exfalso
        exact (Finset.notMem_empty x) ((hafter s hsJ' hslen) ▸ (by
          rw [Finset.mem_sdiff]
          exact ⟨hxD, hx.2⟩))
      · rw [Finset.mem_insert]
        exact Or.inr (hchain s hslen (by
          rw [Finset.mem_sdiff]
          exact ⟨hx.1, hxD⟩))
  · -- hd_eq 扩展到 P ∪ {t₂, J'''}
    intro s hs
    have hsP : s ∉ P := by
      intro hsP
      exact hs (Finset.mem_union.mpr (Or.inl hsP))
    rw [show r s = d s by
      unfold r repairSchedule
      simp [show s ≠ t₂ by
        intro hst
        exact hs (Finset.mem_union.mpr (Or.inr (by simp [hst]))),
        show s ≠ t₂ + 1 + j''' by
        intro hst
        exact hs (Finset.mem_union.mpr (Or.inr (by simp [hst])))]]
    exact hd_eq s hsP
  · -- reduced 界:max hnb (J'''+1)
    have hsup : ∀ s, t₂ + 1 + j''' < s → schedCache d C₀ σ s ⊆ schedCache r C₀ σ s := by
      intro s hs
      exact repairSchedule_superset d σ C₀ hC₀ ht₂ hagree hdis hnoop rfl hj''' (s := s) hs
    intro s hs hfault
    have hnb_le : hnb ≤ s := by omega
    have hJ'''lt : t₂ + 1 + j''' < s := by omega
    have hdsin : d s ∈ schedCache d C₀ σ s := hdred s hnb_le (by
      intro h
      exact hfault (hsup s hJ'''lt h))
    rw [show r s = d s by
      unfold r repairSchedule
      simp [show s ≠ t₂ by omega, show s ≠ t₂ + 1 + j''' by omega]]
    exact hsup s hJ'''lt hdsin

/-- 迭代的情形 B2(活-活子情形):窗口内 resident 分歧 `t₂`(`d t₂` 在
`d` 的 cache 中,`q`、`q''` 都会再次被请求,`j < j''`)处,修复
`r = repairSchedule d t₂ q'' (t₂ + 1 + j'')` 满足:
- 一致到 `t₂ + 1`、miss 不增(`repair_step_swap_strong`,swap 形式由
  `repair_keep_swap_cur` 给出);
- 反向差链扩展到 `insert q'' (Q.image Prod.snd)`(`reverse_diff_chain`);
- 组成不变式 `hd_eq` 扩展到 `P ∪ {t₂, t₂ + 1 + j''}`(`r` 只改这两处);
- reduced 界升到 `max hnb (t₂ + 1 + j'' + 1)`(`repairSchedule_superset_swap`:
  `J''` 后 `D ⊆ Ŝ`,故 `r` 的缺页处 `d` 也缺页,`r s = d s ∈ D ⊆ Ŝ`)。
`hqinE`、`hnotE`、`hnot`、`ht₂notP` 由归纳调用方提供(branch 分析、
Q'' 排除与 no-nop-at-B2 论证,见 DESIGN)。 -/
lemma iterate_main_case_b2_alive (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d_pre t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s →
      d_pre s ∈ schedCache d_pre C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d_pre C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hnb : ℕ) (ht₂hnb : t₂ < hnb)
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : d t₂ ∈ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (d t₂) = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j'')
    (hjj'' : j < j'')
    (Q : Finset (ℕ × Page))
    (hchain : ∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
        schedCache d C₀ σ s ⊆ Q.image Prod.snd)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'')
    (hqinE : d t₂ ∈ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hnotE : ∀ s, t₂ < s → s ≤ t₂ + 1 + j →
      σ.getD s 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s)
    (P : Finset ℕ)
    (ht₂notP : t₂ ∉ P)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hdred : ∀ s, hnb ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s →
      d s ∈ schedCache d C₀ σ s) :
    ∃ r : ℕ → Page,
      agreeWithFIF r C₀ σ (t₂ + 1) ∧
      schedMisses r C₀ σ ≤ schedMisses d C₀ σ ∧
      (∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
          schedCache r C₀ σ s ⊆ insert (fifoSchedule σ C₀ t₂) (Q.image Prod.snd)) ∧
      (∀ s, s ∉ P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
        r s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s) ∧
      (∀ s, max hnb (t₂ + 1 + j'' + 1) ≤ s →
        σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s) := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  let q : Page := d t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule d t₂ q'' (t₂ + 1 + j'')
  have hft : σ.getD t₂ 0 ∉ schedCache e C₀ σ t₂ := by
    intro he
    exact (b2_ehit_ne σ ht₂ Q hpast hQ) (b2_ehit e d σ C₀ hftd (Q.image Prod.snd) (hchain t₂ (by omega)) he)
  have hqq'' : q ≠ q'' := by
    intro hqq
    exact (first_disagree d σ C₀ hC₀ ht₂ hagree hdis).2.1 (by simpa [q, q'', hqq])
  have hswap := repair_keep_swap_cur d_pre d t₀ q₀ q₀' σ C₀ hC₀ hq₀ hqq₀ hweak hft₀ hq₀'res hj₀ hq₀'ne hj₀'
    ht₂ ht₂₀ ht₂₁ hagree hdis hqin hftd hj hj'' hjj'' Q (hchain t₂ (by omega)) hpast hQ hqinE hnotE P
    ht₂notP hnot hd_eq
  have hkept : q ∈ schedCache r C₀ σ (t₂ + 1 + j) := by
    rw [hswap]
    exact Finset.mem_insert_self _ _
  have hqnotE : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → q ∉ schedCache e C₀ σ s := by
    intro s hs1 hs2
    exact swap_q_not_mem e σ C₀ (show e t₂ = q from by
      change exchangeSchedule d_pre t₀ q₀ q₀' σ C₀ t₂ = q
      rw [← hd_eq t₂ ht₂notP]) hqinE hft hj hs1 hs2
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · -- agree 到 t₂+1
    exact (repair_step_swap_strong d σ C₀ hC₀ ht₂ hagree hdis hqin hj hj'' hjj'' hswap).2
  · -- miss 不增
    exact (repair_step_swap_strong d σ C₀ hC₀ ht₂ hagree hdis hqin hj hj'' hjj'' hswap).1
  · -- 链扩展到 insert q'' (Q.image Prod.snd)
    exact reverse_diff_chain e d σ C₀ (show d t₂ = q from rfl) rfl hqin hftd hqq'' hj hj'' hjj''
      hkept (Q.image Prod.snd) hqnotE hchain
  · -- hd_eq 扩展到 P ∪ {t₂, J''}
    intro s hs
    have hsP : s ∉ P := by
      intro hsP
      exact hs (Finset.mem_union.mpr (Or.inl hsP))
    rw [show r s = d s by
      unfold r repairSchedule
      simp [show s ≠ t₂ by
        intro hst
        exact hs (Finset.mem_union.mpr (Or.inr (by simp [hst]))),
        show s ≠ t₂ + 1 + j'' by
        intro hst
        exact hs (Finset.mem_union.mpr (Or.inr (by simp [hst])))]]
    exact hd_eq s hsP
  · -- reduced 界:max hnb (J''+1)
    have hsup : ∀ s, t₂ + 1 + j'' < s → schedCache d C₀ σ s ⊆ schedCache r C₀ σ s := by
      intro s hs
      exact repairSchedule_superset_swap d σ C₀ hC₀ ht₂ hagree hdis hqin rfl (show q = d t₂ from rfl)
        hj hj'' hjj'' (s := s) hs
    intro s hs hfault
    have hnb_le : hnb ≤ s := by omega
    have hJ''lt : t₂ + 1 + j'' < s := by omega
    have hsd : σ.getD s 0 ∉ schedCache d C₀ σ s := by
      intro h
      exact hfault (hsup s hJ''lt h)
    have hdsin : d s ∈ schedCache d C₀ σ s := hdred s hnb_le hsd
    rw [show r s = d s by
      unfold r repairSchedule
      simp [show s ≠ t₂ by omega, show s ≠ t₂ + 1 + j'' by omega]]
    exact hsup s hJ''lt hdsin

/-- 迭代的情形 A(交换步骤):在首个分歧 `t` 处,用策略的选择
`q' = fifoSchedule σ C₀ t` 替换 `d` 的逐出 `q = d t`,得到新调度
`e = exchangeSchedule d t q q' σ C₀`。miss 记账精确:坏事件未发生时
(`q'` 永不再请求,或 `d` 在 `J' = t + 1 + j'` 处缺页)slack 加一
(`exchangeSchedule_misses_le_plus_one`),否则 slack 不变
(`exchangeSchedule_misses_le`);`e` 与 FIF 一致到 `t + 1`
(`exchange_step'`)。当 `q'` 会再次被请求(`hj'`)时,`e` 从 `J' + 1` 起
reduced(`exchangeSchedule_reduced_after`);`q'` 永不再请求时 reduced
结论为空(条件虚真)—— 该情形下交换在至多一个 branch-1 位置
(`d s = q'` 的缺页处)不是 reduced,其界分析是 B5 记录的遗留障碍,
留给 `iterate_main` 装配。 -/
lemma iterate_main_exchange (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (slack : ℕ) :
    ∃ slack',
      agreeWithFIF (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ (t + 1) ∧
      schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ + slack' ≤
        schedMisses d C₀ σ + slack ∧
      ∀ j', nextUse σ (t + 1) (fifoSchedule σ C₀ t) = some j' →
        ∀ s, t + 1 + j' < s →
          σ.getD s 0 ∉ schedCache (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s →
          exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀ s ∈
            schedCache (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s := by
  let q : Page := d t
  let q' : Page := fifoSchedule σ C₀ t
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  have hfd := first_disagree d σ C₀ hC₀ ht hagree hdis
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
  rcases hfifo with hnone | ⟨j, j', hj, hj', hjlt⟩
  · -- q' 永不再请求:一致到 t+1,slack +1(q 会再次被请求)或不变(q 也死)
    have hagree' : agreeWithFIF e C₀ σ (t + 1) := by
      simpa [e, q, q'] using (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    by_cases hqnone : nextUse σ (t + 1) q = none
    · -- q 也永不再请求:miss 不增(exchangeSchedule_misses_le 的 none 枝),slack 不变
      refine ⟨slack, hagree', ?_, ?_⟩
      · have hle' : schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ ≤
            schedMisses d C₀ σ := by
          simpa [e, q, q'] using exchangeSchedule_misses_le d t q q' σ C₀ rfl hqq' hdred hft hq'res
            (Or.inl hnone)
        omega
      · intro j' hj'
        exfalso
        rw [hnone] at hj'
        cases hj'
    · -- q 会再次被请求:坏事件不可能(q' 死),slack + 1
      rcases (Option.ne_none_iff_exists.mp hqnone) with ⟨j, hqopt⟩
      refine ⟨slack + 1, hagree', ?_, ?_⟩
      · have hle' : schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ + 1 ≤
            schedMisses d C₀ σ := by
          simpa [e, q, q'] using exchangeSchedule_misses_le_plus_one d t q q' σ C₀ rfl hqq' hdred
            hft hq'res (Or.inl ⟨hnone, ⟨j, hqopt.symm⟩⟩)
        omega
      · intro j' hj'
        exfalso
        rw [hnone] at hj'
        cases hj'
  · -- q、q' 都会再次被请求
    have hagree' : agreeWithFIF e C₀ σ (t + 1) := by
      simpa [e, q, q'] using (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    have hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact getD_ne_nextUse (k := k) hj' (by omega) (by omega)
    by_cases hbad : σ.getD (t + 1 + j') 0 ∈ schedCache d C₀ σ (t + 1 + j')
    · -- 坏事件发生:slack 不变
      refine ⟨slack, hagree', ?_, ?_⟩
      · have hle' : schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ ≤
            schedMisses d C₀ σ := by
          simpa [e, q, q'] using exchangeSchedule_misses_le d t q q' σ C₀ rfl hqq' hdred hft hq'res
            (Or.inr ⟨j, j', hj, hj', hjlt⟩)
        omega
      · intro j0 hj0
        have hj0eq : j0 = j' := Option.some.inj (hj0.symm.trans hj')
        intro s hs hFault
        have hred := exchangeSchedule_reduced_after d t q q' σ C₀ rfl hqq' hdred hft hq'res hj hq'ne
          (j' := j') hj' (s := s) (by omega) hFault
        simpa [e, q, q'] using hred
    · -- 坏事件未发生:slack + 1
      refine ⟨slack + 1, hagree', ?_, ?_⟩
      · have hle' : schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ + 1 ≤
            schedMisses d C₀ σ := by
          simpa [e, q, q'] using exchangeSchedule_misses_le_plus_one d t q q' σ C₀ rfl hqq' hdred
            hft hq'res (Or.inr ⟨j, j', hj, hj', hjlt, hbad⟩)
        omega
      · intro j0 hj0
        have hj0eq : j0 = j' := Option.some.inj (hj0.symm.trans hj')
        intro s hs hFault
        have hred := exchangeSchedule_reduced_after d t q q' σ C₀ rfl hqq' hdred hft hq'res hj hq'ne
          (j' := j') hj' (s := s) (by omega) hFault
        simpa [e, q, q'] using hred

/-- FIF 在 `t` 处的逐出页 `p`(FIF 在分歧处缺页并逐出)在首次请求
`J = t + 1 + j` 之前不在 FIF 自己的 cache 中:基步由 `hftF` 缺页 + `p`
residence 给出,之后 `nextUse` 排除请求、cache 只进请求页。 -/
lemma fifo_evict_absent_until_request (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (hftF : σ.getD t 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ t)
    {p : Page} (hp : p = fifoSchedule σ C₀ t)
    {j : ℕ} (hj : nextUse σ (t + 1) p = some j) :
    ∀ s, t < s → s ≤ t + 1 + j → p ∉ schedCache (fifoSchedule σ C₀) C₀ σ s := by
  let F : ℕ → Finset Page := schedCache (fifoSchedule σ C₀) C₀ σ
  have hp_mem : p ∈ F t := by
    dsimp [F]
    rw [hp]
    rw [schedCache_fifoSchedule]
    change (fifoPolicy σ).evict t (cacheSeq (fifoPolicy σ) C₀ σ t) (σ.getD t 0) ∈
      cacheSeq (fifoPolicy σ) C₀ σ t
    exact (fifoPolicy σ).evict_mem t (cacheSeq (fifoPolicy σ) C₀ σ t) (σ.getD t 0)
      (by simpa [schedCache_fifoSchedule] using hftF) (cacheSeq_nonempty (fifoPolicy σ) C₀ σ t hC₀)
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs1 hs2
      by_cases hs_eq : s = t
      · -- 基步:s+1 = t+1,cache 逐出 p 且请求 σ[t] ≠ p
        subst s
        rw [schedCache]
        rw [if_neg hftF]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hpeq | hmem
        · exact hftF (hpeq ▸ hp_mem)
        · exact (Finset.mem_erase.mp hmem).1 hp
      · -- 步:请求 σ[s] ≠ p,且 p ∉ F_s(归纳),故 p ∉ F_{s+1}
        have hst : t < s := by omega
        have hih : p ∉ F s := ih (by omega) (by omega)
        have hneq : σ.getD s 0 ≠ p := getD_ne_nextUse (k := s) hj (by omega) (by omega)
        rw [schedCache]
        by_cases hhit : σ.getD s 0 ∈ F s
        · rw [if_pos hhit]
          exact hih
        · rw [if_neg hhit]
          intro hmem
          rcases Finset.mem_insert.mp hmem with hpeq | hmem
          · exact hneq hpeq.symm
          · exact hih (Finset.mem_erase.mp hmem).2

/-- nop 位置 `s`(某对 `(tₗ, qₗ)` 的 nop `s = tₗ + 1 + jₗ`)处,当前调度 `d`
的逐出是 no-op:`d s ∉ D_s`。`hcomp` 给 `d s = qₗ`,而 `qₗ` 是 FIF 在 `tₗ`
的逐出页(`hQfifo`),首次请求在 `s`(`fifo_evict_absent_until_request` +
与 FIF 一致到 `s`)故 `qₗ ∉ D_s`。 -/
lemma nop_position_noop (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (d : ℕ → Page)
    {t₂ : ℕ} (hagree : agreeWithFIF d C₀ σ t₂)
    (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (t0 : ℕ)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t0)
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q''))
    (hpair : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = some j'' →
      σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧ q'' ∈ schedCache d C₀ σ tᵢ ∧ d tᵢ = q'')
    (hQfifo : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = fifoSchedule σ C₀ tᵢ)
    {s : ℕ} (ht₀s : t0 < s) (hs : s ≤ t₂) (hsP : s ∈ P) :
    d s ∉ schedCache d C₀ σ s := by
  rcases hcomp s hsP with hc1 | hc2
  · -- s 也是某对的修复位置:与 hpast(tₗ < t0 < s = tₗ)矛盾
    rcases hc1 with ⟨tₗ, qₗ, htqₗ, hteqₗ, hdtₗ⟩
    have htₗt0 : tₗ < t0 := hpast tₗ qₗ htqₗ
    omega
  · -- nop 位置:d s = qₗ,而 qₗ ∉ D_s(FIF 在 tₗ 逐出,首次请求在 s)
    rcases hc2 with ⟨tₗ, qₗ, jₗ, htqₗ, hnextₗ, hteqₗ, hdtₗ⟩
    intro hdsin
    have hftFₗ : σ.getD tₗ 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ tₗ := by
      have hftdₗ := (hpair tₗ qₗ jₗ htqₗ hnextₗ).1
      rw [← hagree tₗ (by omega)]
      exact hftdₗ
    have habsₗ := fifo_evict_absent_until_request σ C₀ hC₀ hftFₗ (hQfifo tₗ qₗ htqₗ) hnextₗ
    have hqₗnotD : qₗ ∉ schedCache d C₀ σ s := by
      intro hq
      have hqF : qₗ ∈ schedCache (fifoSchedule σ C₀) C₀ σ s := by
        rw [← hagree s hs]
        exact hq
      exact habsₗ s (by omega) (by omega) hqF
    exact hqₗnotD (hdtₗ ▸ hdsin)

/-- hQ 的严格化:首个分歧 `t₂` 处(`t₂` 是 B2 resident,`d t₂ ∈ D_{t₂}`),
过往修复对 `(tᵢ, q''ᵢ)` 的首次请求 `J''ᵢ = tᵢ + 1 + j''ᵢ` 严格在 `t₂` 之后:
`J''ᵢ < t₂` 时,`J''ᵢ` 处的请求对 d 是 nop(逐出 `q''ᵢ` 不在 cache),而 FIF
在 `J''ᵢ` 的逐出页 `f` 属于 `D_{J''ᵢ+1}`(d 的 no-op 只加 `q''ᵢ`)但不属于
`F_{J''ᵢ+1}`(FIF 换出 `f`)—— 与 `J''ᵢ + 1 ≤ t₂` 处的一致矛盾;`J''ᵢ = t₂`
时 `σ[t₂] = q''ᵢ` 且 `d t₂ ∉ D_{t₂}`(`nop_position_noop`)—— 与 B2
resident 矛盾。给出 B2 步骤所需的 `t₂ < J''ᵢ` 严格形式。 -/
lemma past_pair_first_request_after (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (d : ℕ → Page)
    (t0 t₂ : ℕ) (ht₀t₂ : t0 ≤ t₂)
    (hagree : agreeWithFIF d C₀ σ t₂)
    (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t0)
    (hP : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j''))
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q''))
    (hpair : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = some j'' →
      σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧ q'' ∈ schedCache d C₀ σ tᵢ ∧ d tᵢ = q'')
    (hQfifo : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = fifoSchedule σ C₀ tᵢ)
    (hP_in : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ P)
    (hQ₀ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t0 < tᵢ + 1 + j'')
    (ht₂ : t₂ < σ.length)
    (hqin : d t₂ ∈ schedCache d C₀ σ t₂) :
    ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'' := by
  intro tᵢ q'' htq
  rcases hQ₀ tᵢ q'' htq with hdead | ⟨j'', hnext, ht₀J⟩
  · exact Or.inl hdead
  · right
    refine ⟨j'', hnext, ?_⟩
    by_contra hJle
    have hJ : tᵢ + 1 + j'' ≤ t₂ := by omega
    have hget : σ.getD (tᵢ + 1 + j'') 0 = q'' := getD_eq_nextUse hnext
    have htᵢt₂ : tᵢ ≤ t₂ := le_trans (le_of_lt (hpast tᵢ q'' htq)) ht₀t₂
    have hftF : σ.getD tᵢ 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ tᵢ := by
      have hftd := (hpair tᵢ q'' j'' htq hnext).1
      rw [← hagree tᵢ htᵢt₂]
      exact hftd
    have habs := fifo_evict_absent_until_request σ C₀ hC₀ hftF (hQfifo tᵢ q'' htq) hnext
    by_cases hJlt : tᵢ + 1 + j'' < t₂
    · -- J''ᵢ < t₂:J''ᵢ + 1 ≤ t₂ 处 cache 分歧
      let s : ℕ := tᵢ + 1 + j''
      have hst₂ : s ≤ t₂ := by dsimp [s]; omega
      have htᵢs : tᵢ < s := by dsimp [s]; omega
      have ht₀s : t0 < s := by dsimp [s]; omega
      have hget' : σ.getD s 0 = q'' := by
        dsimp [s]
        exact getD_eq_nextUse hnext
      have hq''notD : q'' ∉ schedCache d C₀ σ s := by
        intro hq
        have hqF : q'' ∈ schedCache (fifoSchedule σ C₀) C₀ σ s := by
          rw [← hagree s hst₂]
          exact hq
        exact habs s htᵢs le_rfl hqF
      have hsigD : σ.getD s 0 ∉ schedCache d C₀ σ s := by
        intro hmem
        rw [hget'] at hmem
        exact hq''notD hmem
      have hsigF : σ.getD s 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ s := by
        intro hmem
        rw [hget'] at hmem
        exact habs s htᵢs le_rfl hmem
      have hnoop : d s ∉ schedCache d C₀ σ s := nop_position_noop σ C₀ hC₀ d (t₂ := t₂) hagree
        Q P t0 hpast hcomp hpair hQfifo (ht₀s := ht₀s) (hs := hst₂)
        (hP_in s (Or.inr ⟨tᵢ, q'', j'', htq, hnext, rfl⟩))
      have hf_memF : fifoSchedule σ C₀ s ∈ schedCache (fifoSchedule σ C₀) C₀ σ s := by
        rw [schedCache_fifoSchedule]
        change (fifoPolicy σ).evict s (cacheSeq (fifoPolicy σ) C₀ σ s) (σ.getD s 0) ∈
          cacheSeq (fifoPolicy σ) C₀ σ s
        exact (fifoPolicy σ).evict_mem s (cacheSeq (fifoPolicy σ) C₀ σ s) (σ.getD s 0)
          (by simpa [schedCache_fifoSchedule] using hsigF) (cacheSeq_nonempty (fifoPolicy σ) C₀ σ s hC₀)
      have hf_memD : fifoSchedule σ C₀ s ∈ schedCache d C₀ σ s := by
        rw [hagree s hst₂]
        exact hf_memF
      have hf_memD1 : fifoSchedule σ C₀ s ∈ schedCache d C₀ σ (s + 1) := by
        rw [schedCache]
        rw [if_neg hsigD]
        rw [Finset.mem_insert]
        right
        rw [Finset.mem_erase]
        constructor
        · intro hfeq
          rw [hfeq] at hf_memD
          exact hnoop hf_memD
        · exact hf_memD
      have hs1 : s + 1 ≤ t₂ := by dsimp [s]; omega
      have hf_notF1 : fifoSchedule σ C₀ s ∉ schedCache (fifoSchedule σ C₀) C₀ σ (s + 1) := by
        rw [schedCache]
        rw [if_neg hsigF]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hfeq | hmem
        · rw [hfeq] at hf_memF
          exact hsigF hf_memF
        · exact (Finset.mem_erase.mp hmem).1 rfl
      exact hf_notF1 (by rw [← hagree (s + 1) hs1]; exact hf_memD1)
    · -- J''ᵢ = t₂:σ[t₂] = q''ᵢ 且 d t₂ ∉ D_{t₂}(nop),与 hqin 矛盾
      have hs_eq : tᵢ + 1 + j'' = t₂ := by omega
      have ht₀t₂' : t0 < t₂ := by omega
      have hnoop : d t₂ ∉ schedCache d C₀ σ t₂ := nop_position_noop σ C₀ hC₀ d (t₂ := t₂) hagree
        Q P t0 hpast hcomp hpair hQfifo (ht₀s := ht₀t₂') (hs := le_rfl)
        (hP_in t₂ (Or.inr ⟨tᵢ, q'', j'', htq, hnext, hs_eq.symm⟩))
      exact hnoop hqin

/- ### q₀'-B1 的 slack 供应(bad ≤ slack 的 q₀' 半边)

分支 1 反向:交换在 `s > t` 处逐出 `q'` 当且仅当源 `d` 于 `s` 逐出 `q'`
(`exchangeDecision` 的分支 1;其它分支逐出 `E` 中的页或 `d s`,由
`q' ∉ E` 与缺页 + 基数论证排除 `else 0`)。由
`b1_exchange_no_bad_q0`:窗口内 `d t₂ = q₀'` 的 B1 位置(`t₂ ∉ P`,源与
交换都在 `t₂` 缺页)是窗口内首个分支 1(`window_branch1_once`),故源对
`q₀'` 的逐出是真逐出(`q₀' ∈ D₀_{t₂}` —— 从 `t₀+1` 起的正向归纳:无分支 1
即无逐出、请求 `≠ q₀'`),由 `evicted_page_absent_until_request` 的归纳
(t₂ 版本,直接用 `hj'₀` 的界)得 `q₀' ∉ D₀_{J'₀}` —— 交换的坏事件未发生。
`b1_bad_le_slack_q0` 由此给出 `bad ≤ slack`(坏事件发生时 `slack ≥ 1`)。 -/

/-- 分支 1 反向:交换在 `s > t` 处逐出 `q'` ⟹ 源 `d` 于 `s` 逐出 `q'`。
`exchangeDecision` 的结构:分支 1 逐出 `q'`;分支 4-6 逐出 `E − D` 中的页
(`q' ∉ E` 矛盾);`else 0` 由缺页 + 基数论证排除。 -/
lemma exchangeSchedule_eq_q'_imp_d_eq_q' (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hs1 : t < s)
    (hq'notE : q' ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s)
    (hFault : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s)
    (heq : (exchangeSchedule d t q q' σ C₀) s = q') :
    d s = q' := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  have heqCore : (exchangeScheduleCore d t q q' σ C₀ s).2 = q' := by
    change (exchangeSchedule d t q q' σ C₀) s = q'
    exact heq
  rw [exchangeScheduleCore_second] at heqCore
  rw [← schedCache_exchangeScheduleCore] at heqCore
  change exchangeDecision d t q q' σ C₀ (schedCache e C₀ σ s) s = q' at heqCore
  unfold exchangeDecision at heqCore
  rw [if_neg (by omega)] at heqCore
  rw [if_neg (by omega)] at heqCore
  by_cases h1 : d s = q'
  · exact h1
  · rw [if_neg h1] at heqCore
    by_cases hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧ σ.getD s 0 ∈ schedCache d C₀ σ s
    · rw [if_pos hb4] at heqCore
      let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
      by_cases hf : (M.filter (fun x => x ≠ q')).Nonempty
      · rw [dif_pos hf] at heqCore
        exfalso
        exact (Finset.mem_filter.mp (Classical.choose_spec hf)).2 heqCore
      · by_cases hm : M.Nonempty
        · rw [dif_neg hf] at heqCore
          rw [dif_pos hm] at heqCore
          exfalso
          have hq'C : q' ∈ schedCache e C₀ σ s := by
            have hmem : Classical.choose hm ∈ schedCache e C₀ σ s :=
              (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
            rwa [heqCore] at hmem
          exact hq'notE hq'C
        · rw [dif_neg hf] at heqCore
          rw [dif_neg hm] at heqCore
          exfalso
          have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
            rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t q q' σ C₀ s).1 by
              rw [← schedCache_exchangeScheduleCore]]
            exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
          have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          exact hFault (hEq.symm ▸ hb4.2)
    · rw [if_neg hb4] at heqCore
      by_cases hdsin : d s ∈ schedCache e C₀ σ s
      · rw [if_pos hdsin] at heqCore
        exact heqCore
      · rw [if_neg hdsin] at heqCore
        let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
        by_cases hm : M.Nonempty
        · rw [dif_pos hm] at heqCore
          exfalso
          have hq'C : q' ∈ schedCache e C₀ σ s := by
            have hmem : Classical.choose hm ∈ schedCache e C₀ σ s :=
              (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
            rwa [heqCore] at hmem
          exact hq'notE hq'C
        · rw [dif_neg hm] at heqCore
          exfalso
          have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
            rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t q q' σ C₀ s).1 by
              rw [← schedCache_exchangeScheduleCore]]
            exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
          have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          have hdFault : σ.getD s 0 ∉ schedCache d C₀ σ s := by
            intro h
            exact hFault (hEq.symm ▸ h)
          have hdsE : d s ∈ schedCache d C₀ σ s := hweak s (by omega) hdFault
          exact hdsin (hEq.symm ▸ hdsE)

/-- q₀'-B1 的 slack 供应:窗口内 `d t₂ = q₀'` 的 B1 位置(`t₂ ∉ P`,源与交换
都在 `t₂` 缺页)使交换的坏事件不发生:`q₀' ∉ D₀_{J'₀}`。`d t₂ = q₀'` 经
分支 1 反向给出源的 `d_pre t₂ = q₀'`;`window_branch1_once` 给出 `t₂` 是
窗口内首个分支 1,故源对 `q₀'` 的逐出是真逐出(正向归纳:从 `t₀+1` 起无
`q₀'` 逐出、请求 `≠ q₀'`),再由 `evicted_page_absent_until_request` 的
t₂ 版本(直接用 `hj'₀` 的界)得 `q₀'` 在 `(t₂, J'₀]` 缺席。 -/
lemma b1_exchange_no_bad_q0 (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq₀ : d_pre t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s →
      d_pre s ∈ schedCache d_pre C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀)
    (hq'res : q₀' ∈ schedCache d_pre C₀ σ t₀)
    {j₀' : ℕ} (hj' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₀t₂ : t₀ < t₂) (ht₂J : t₂ < t₀ + 1 + j₀')
    (hd : d t₂ = q₀')
    (P : Finset ℕ) (ht₂notP : t₂ ∉ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hFault : σ.getD t₂ 0 ∉ schedCache d_pre C₀ σ t₂)
    (hFaultE : σ.getD t₂ 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂) :
    σ.getD (t₀ + 1 + j₀') 0 ∉ schedCache d_pre C₀ σ (t₀ + 1 + j₀') := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  -- 1. 分支 1 反向:d_pre t₂ = q₀'
  have hq'notE : q₀' ∉ schedCache e C₀ σ t₂ := by
    dsimp [e]
    exact exchangeSchedule_q'_absent d_pre t₀ q₀ q₀' σ C₀ hweak hft₀ hq'res hj' ht₀t₂ (le_of_lt ht₂J)
  have hdpre : d_pre t₂ = q₀' := by
    exact exchangeSchedule_eq_q'_imp_d_eq_q' d_pre t₀ q₀ q₀' σ C₀ hweak ht₀t₂ hq'notE hFaultE
      ((hd_eq t₂ ht₂notP).symm.trans hd)
  -- 2. t₂ 是窗口内首个分支 1:∀ s ∈ (t₀, t₂),缺页 ⟹ d_pre s ≠ q₀'
  have hfirst : ∀ s, t₀ < s → s < t₂ → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ≠ q₀' := by
    intro s hs1 hs2 hFaults
    intro hbs
    exact window_branch1_once d_pre t₀ q₀ q₀' σ C₀ hweak hq'res hj'
      hs1 (by omega) ht₀t₂ (by omega) (by omega) hbs hdpre hFaults hFault
  -- 3. 真逐出:q₀' ∈ D₀_{t₂}(从 t₀+1 起无 q₀' 逐出、请求 ≠ q₀')
  have hq'keep : q₀' ∈ schedCache d_pre C₀ σ t₂ := by
    have hmain : ∀ s, t₀ + 1 ≤ s → s ≤ t₂ → q₀' ∈ schedCache d_pre C₀ σ s := by
      intro s
      induction s with
      | zero => omega
      | succ s ih =>
          intro hs1 hs2
          by_cases hst : s = t₀
          · -- 基步:s+1 = t₀+1,源逐出 q₀(≠ q₀'),q₀' 保留
            subst s
            rw [schedCache]
            rw [if_neg hft₀]
            rw [Finset.mem_insert]
            right
            rw [Finset.mem_erase]
            constructor
            · intro hqeq
              exact hqq₀ ((hqeq.trans hq₀).symm)
            · exact hq'res
          · -- 步:请求 σ[s] ≠ q₀',且 s 处无 q₀' 逐出(分支 1 排除)
            have hs1' : t₀ + 1 ≤ s := by omega
            have hs2' : s ≤ t₂ := by omega
            have hqin : q₀' ∈ schedCache d_pre C₀ σ s := ih hs1' hs2'
            have hneq : σ.getD s 0 ≠ q₀' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
            by_cases hf : σ.getD s 0 ∈ schedCache d_pre C₀ σ s
            · -- 命中:cache 不变
              rw [schedCache]
              rw [if_pos hf]
              exact hqin
            · -- 缺页:d_pre s ≠ q₀'(hfirst),故 q₀' 保留
              rw [schedCache]
              rw [if_neg hf]
              rw [Finset.mem_insert]
              right
              rw [Finset.mem_erase]
              constructor
              · intro hqeq
                exact hfirst s (by omega) (by omega) hf hqeq.symm
              · exact hqin
    exact hmain t₂ (by omega) le_rfl
  -- 4. evicted_page_absent_until_request 的 t₂ 版本:q₀' ∉ D₀_s on (t₂, J'₀]
  have habs : ∀ s, t₂ < s → s ≤ t₀ + 1 + j₀' → q₀' ∉ schedCache d_pre C₀ σ s := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hst : s = t₂
        · -- 基步:s+1 = t₂+1,cache 逐出 q₀' 且请求 σ[t₂] ≠ q₀'
          subst s
          rw [schedCache]
          rw [if_neg hFault]
          rw [hdpre]
          intro hm
          rcases Finset.mem_insert.mp hm with hqeq | hm
          · exact hFault (show σ.getD t₂ 0 ∈ schedCache d_pre C₀ σ t₂ from by rwa [← hqeq])
          · exact (Finset.mem_erase.mp hm).1 rfl
        · -- 步:q₀' ∉ D_s(归纳),且请求 σ[s] ≠ q₀'
          have hs1' : t₂ < s := by omega
          have hs2' : s ≤ t₀ + 1 + j₀' := by omega
          have hqnot : q₀' ∉ schedCache d_pre C₀ σ s := ih (by omega) (by omega)
          have hneq : σ.getD s 0 ≠ q₀' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
          rw [schedCache]
          by_cases hr : σ.getD s 0 ∈ schedCache d_pre C₀ σ s
          · rw [if_pos hr]
            exact hqnot
          · rw [if_neg hr]
            intro hm
            rcases Finset.mem_insert.mp hm with hqeq | hm
            · exact hneq hqeq.symm
            · exact hqnot (Finset.mem_erase.mp hm).2
  -- 5. σ[J'₀] = q₀',故坏事件(σ[J'₀] ∈ D₀_{J'₀})不发生
  intro hbad
  have hsig : σ.getD (t₀ + 1 + j₀') 0 = q₀' := getD_eq_nextUse hj'
  exact habs (t₀ + 1 + j₀') (by omega) le_rfl (hsig ▸ hbad)

/-- q₀'-B1 的 slack 不变式:`bad ≤ slack`。坏事件(`σ[J'''] ∈ D_{J'''}`)
发生时 `bad = 1`,由 `hslack`(`1 ≤ slack` —— 交换的坏事件未发生时
`exchange_step_slack` 给出 `slack' = slack + 1`,且 q₀'-B1 是窗口内第一步,
无中间消耗)得 `bad ≤ slack`。 -/
lemma b1_bad_le_slack_q0 (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq₀ : d_pre t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s →
      d_pre s ∈ schedCache d_pre C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀)
    (hq'res : q₀' ∈ schedCache d_pre C₀ σ t₀)
    {j₀' : ℕ} (hj' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₀t₂ : t₀ < t₂) (ht₂J : t₂ < t₀ + 1 + j₀')
    (hd : d t₂ = q₀')
    (P : Finset ℕ) (ht₂notP : t₂ ∉ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hFault : σ.getD t₂ 0 ∉ schedCache d_pre C₀ σ t₂)
    (hFaultE : σ.getD t₂ 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''')
    (slack : ℕ) (hslack : 1 ≤ slack) :
    (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''') then 1 else 0) ≤ slack := by
  by_cases hbad : σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''')
  · rw [if_pos hbad]
    exact hslack
  · rw [if_neg hbad]
    omega

/-- 死页修复 `r = repairSchedule e t q'' t` 的 `q''` 缺席:`q''` 于 `t` 被逐出,
永不再请求,故 `q'' ∉ Ŝ_s` 对 `t < s < σ.length` 恒成立。 -/
lemma repair_q''_absent_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    {q'' : Page} (hq''in : q'' ∈ schedCache e C₀ σ t) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hq''dead : nextUse σ (t + 1) q'' = none) :
    ∀ s, t < s → s < σ.length → q'' ∉ schedCache (repairSchedule e t q'' t) C₀ σ s := by
  let r : ℕ → Page := repairSchedule e t q'' t
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs1 hslt
      by_cases hs_eq : s = t
      · -- 基步:s+1 = t+1
        subst s
        have hsig_ne : σ.getD t 0 ≠ q'' := by
          intro hsig
          exact hft (hsig ▸ hq''in)
        have hftS : σ.getD t 0 ∉ schedCache r C₀ σ t := by
          rw [schedCache_repairSchedule_eq_e_qp_dead e t q'' σ C₀ (le_rfl)]
          exact hft
        rw [schedCache]
        rw [if_neg hftS]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hpeq | hmem
        · exact hsig_ne hpeq.symm
        · exact (Finset.mem_erase.mp hmem).1 (repairSchedule_at_t e t q'' t).symm
      · -- 步:请求 σ[s] ≠ q'',且 q'' ∉ S_s(归纳),故 q'' ∉ S_{s+1}
        have hst' : t < s := by omega
        have hih : q'' ∉ schedCache r C₀ σ s := ih (by omega) (by omega)
        have hneq : σ.getD s 0 ≠ q'' := getD_ne_of_nextUse_none σ hq''dead (by omega) (by omega)
        rw [schedCache]
        by_cases hhit : σ.getD s 0 ∈ schedCache r C₀ σ s
        · rw [if_pos hhit]
          exact hih
        · rw [if_neg hhit]
          intro hmem
          rcases Finset.mem_insert.mp hmem with hpeq | hmem
          · exact hneq hpeq.symm
          · exact hih (Finset.mem_erase.mp hmem).2

/-- 死页缺席(s ≥ σ.length 版):`q'' ≠ 0` 时 `σ.getD s 0 = 0 ≠ q''`,请求避开
`q''`,缺席对所有 `s > t` 成立。 -/
lemma repair_q''_absent_dead_long (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    {q'' : Page} (hq''in : q'' ∈ schedCache e C₀ σ t) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hq''dead : nextUse σ (t + 1) q'' = none)
    {s : ℕ} (hst : t < s) (hq0 : q'' ≠ 0) :
    q'' ∉ schedCache (repairSchedule e t q'' t) C₀ σ s := by
  let r : ℕ → Page := repairSchedule e t q'' t
  have hmain : ∀ s, t < s → q'' ≠ 0 → q'' ∉ schedCache r C₀ σ s := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hst hq0
        by_cases hs_eq : s = t
        · -- 基步:s+1 = t+1
          subst s
          have hsig_ne : σ.getD t 0 ≠ q'' := by
            intro hsig
            exact hft (hsig ▸ hq''in)
          have hftS : σ.getD t 0 ∉ schedCache r C₀ σ t := by
            rw [schedCache_repairSchedule_eq_e_qp_dead e t q'' σ C₀ (le_rfl)]
            exact hft
          rw [schedCache]
          rw [if_neg hftS]
          intro hmem
          rcases Finset.mem_insert.mp hmem with hpeq | hmem
          · exact hsig_ne hpeq.symm
          · exact (Finset.mem_erase.mp hmem).1 (repairSchedule_at_t e t q'' t).symm
        · -- 步:请求 σ[s] ≠ q''(s < σ.length 用 nextUse,s ≥ σ.length 时 σ[s] = 0 ≠ q''),
          -- 且 q'' ∉ S_s(归纳),故 q'' ∉ S_{s+1}
          have hst' : t < s := by omega
          have hih : q'' ∉ schedCache r C₀ σ s := ih (by omega) hq0
          have hneq : σ.getD s 0 ≠ q'' := by
            by_cases hslt : s < σ.length
            · exact getD_ne_of_nextUse_none σ hq''dead (by omega) hslt
            · have hsig0 : σ.getD s 0 = 0 := by simp [hslt]
              intro hsigq
              exact hq0 (hsig0.symm.trans hsigq).symm
          rw [schedCache]
          by_cases hhit : σ.getD s 0 ∈ schedCache r C₀ σ s
          · rw [if_pos hhit]
            exact hih
          · rw [if_neg hhit]
            intro hmem
            rcases Finset.mem_insert.mp hmem with hpeq | hmem
            · exact hneq hpeq.symm
            · exact hih (Finset.mem_erase.mp hmem).2
  exact hmain s hst hq0

/-- 情形 B1 死页版:no-op 分歧 `t₂` 处 `q'' = fifoSchedule σ C₀ t₂` 永不再
请求(`hq''dead`)时,死页修复 `r = repairSchedule d t₂ q'' t₂`(nop 即 `t₂`)
满足:一致到 `t₂ + 1`(`repair_step_qp_dead`)、miss 不增(免费,无坏事件)、
链扩展到 `insert q'' (Q.image Prod.snd)`(`repair_diff_noop_qp_dead` 的
`E − Ŝ ⊆ {q''}`)、`hd_eq` 扩展到 `P ∪ {t₂}`、reduced 界保持 `hnb`。 -/
lemma iterate_main_case_b1_dead (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length)
    (hnb : ℕ) (ht₂hnb : t₂ < hnb)
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : d t₂ ∉ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    (hq''dead : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = none)
    (Q : Finset (ℕ × Page))
    (hchain : ∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
        schedCache d C₀ σ s ⊆ Q.image Prod.snd)
    (P : Finset ℕ)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hdred : ∀ s, hnb ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hdnoevict : ∀ s, hnb ≤ s → d s ≠ fifoSchedule σ C₀ t₂) :
    ∃ r : ℕ → Page,
      agreeWithFIF r C₀ σ (t₂ + 1) ∧
      schedMisses r C₀ σ ≤ schedMisses d C₀ σ ∧
      (∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
          schedCache r C₀ σ s ⊆ insert (fifoSchedule σ C₀ t₂) (Q.image Prod.snd)) ∧
      (∀ s, s ∉ P ∪ ({t₂} : Finset ℕ) → r s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s) ∧
      (∀ s, hnb ≤ s → s < σ.length → σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s) := by
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule d t₂ q'' t₂
  have hstep := repair_step_qp_dead d σ C₀ hC₀ ht₂ hagree hdis hnoop hq''dead
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · -- agree 到 t₂+1
    exact hstep.2
  · -- miss 不增(免费)
    exact hstep.1
  · -- 链:E − Ŝ ⊆ insert q'' (Q.image)
    intro s hs
    intro x hx
    rw [Finset.mem_sdiff] at hx
    have hdiff := repair_diff_noop_qp_dead d σ C₀ hnoop hftd rfl hq''dead s hs
    rw [Finset.mem_insert]
    by_cases hxq : x = q''
    · exact Or.inl hxq
    · right
      have hxD : x ∉ schedCache d C₀ σ s := by
        intro hxd
        have hxdiff : x ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
          rw [Finset.mem_sdiff]
          exact ⟨hxd, hx.2⟩
        exact hxq (Finset.mem_singleton.mp (hdiff.1 hxdiff))
      exact hchain s hs (by
        rw [Finset.mem_sdiff]
        exact ⟨hx.1, hxD⟩)
  · -- hd_eq 扩展到 P ∪ {t₂}
    intro s hs
    have hsP : s ∉ P := by
      intro hsP
      exact hs (Finset.mem_union.mpr (Or.inl hsP))
    have hsne : s ≠ t₂ := by
      intro hst
      exact hs (Finset.mem_union.mpr (Or.inr (by simp [hst])))
    rw [show r s = d s by
      unfold r repairSchedule
      simp [hsne]]
    exact hd_eq s hsP
  · -- reduced 界保持 hnb:r = d off {t₂},t₂ 处 q'' resident
    intro s hs hslt hfault
    by_cases hs_eq : s = t₂
    · subst s
      have hq''in : q'' ∈ schedCache d C₀ σ t₂ := by
        dsimp [q'']
        exact (first_disagree d σ C₀ hC₀ ht₂ hagree hdis).2.2
      change repairSchedule d t₂ (fifoSchedule σ C₀ t₂) t₂ t₂ ∈
        schedCache (repairSchedule d t₂ (fifoSchedule σ C₀ t₂) t₂) C₀ σ t₂
      rw [schedCache_repairSchedule_eq_e_qp_dead d t₂ (fifoSchedule σ C₀ t₂) σ C₀ (le_rfl)]
      simpa [repairSchedule_at_t] using hq''in
    · -- s ≠ t₂:r s = d s;D − Ŝ ⊆ {q''},故 d s ∈ Ŝ_s 除非 d s = q''
      have hdiff := repair_diff_noop_qp_dead d σ C₀ hnoop hftd rfl hq''dead s (by omega)
      have hfaultD : σ.getD s 0 ∉ schedCache d C₀ σ s := by
        intro hsig
        have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
          rw [Finset.mem_sdiff]
          exact ⟨hsig, hfault⟩
        have hsigq := Finset.mem_singleton.mp (hdiff.1 hmem)
        have hsigqF : σ.getD s 0 = fifoSchedule σ C₀ t₂ := by
          simpa [q''] using hsigq
        exact getD_ne_of_nextUse_none σ hq''dead (le_trans (Nat.succ_le_of_lt ht₂hnb) hs) hslt hsigqF
      have hred := hdred s hs hfaultD
      rw [show r s = d s by
        unfold r repairSchedule
        simp [hs_eq]]
      by_cases hdsq : d s = q''
      · -- d s = q'':与 hdnoevict(当前调度永不逐出 q'')矛盾
        exfalso
        exact hdnoevict s hs (hdsq.trans (by dsimp [q'']))
      · -- d s ≠ q'':反证:d s ∉ Ŝ_s 则 d s ∈ D − Ŝ ⊆ {q''},矛盾
        by_contra hnotS
        have hmem : d s ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
          rw [Finset.mem_sdiff]
          exact ⟨hred, hnotS⟩
        exact hdsq (Finset.mem_singleton.mp (hdiff.1 hmem))
/-- 当前窗口的交换调度:`win = none`(尚未交换)时取回退调度 `fb`
(此时链/逐出一致不变式平凡),`win = some (d_pre, t₀, q₀, q₀', j₀, j₀')`
时为该窗口的交换调度。 -/
private noncomputable def windowExchange (win : Option ((ℕ → Page) × ℕ × Page × Page × ℕ × ℕ))
    (fb : ℕ → Page) (σ : List Page) (C₀ : Finset Page) : ℕ → Page :=
  match win with
  | none => fb
  | some w => exchangeSchedule w.1 w.2.1 w.2.2.1 w.2.2.2.1 σ C₀

/-- IterateState: state (d, t0, slack, hnb, Q, P) plus window, invariants per DESIGN. -/
private structure IterateState (σ : List Page) (C₀ : Finset Page) (M : ℕ) where
  d : ℕ → Page
  t0 : ℕ
  slack : ℕ
  hnb : ℕ
  Q : Finset (ℕ × Page)
  P : Finset ℕ
  win : Option ((ℕ → Page) × ℕ × Page × Page × ℕ × ℕ)
  hwin_inv : ∀ (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ),
    win = some (d_pre, t₀, q₀, q₀', j₀, j₀') →
    t₀ < t0 ∧ d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
    (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
    σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
    nextUse σ (t₀ + 1) q₀ = some j₀ ∧
    (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
    nextUse σ (t₀ + 1) q₀' = some j₀'
  hagree : agreeWithFIF d C₀ σ t0
  hbook : schedMisses d C₀ σ + slack ≤ M
  hchain : ∀ s, s ≤ σ.length → schedCache (windowExchange win d σ C₀) C₀ σ s \
      schedCache d C₀ σ s ⊆ Q.image Prod.snd
  hd_eq : ∀ s, s ∉ P → d s = windowExchange win d σ C₀ s
  hdred : ∀ s, hnb ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s
  hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t0
  hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
    nextUse σ (tᵢ + 1) q'' = none ∨
      ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t0 < tᵢ + 1 + j''
  hQfifo : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = fifoSchedule σ C₀ tᵢ
  hP : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
    (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
      nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'')
  hP_in : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
    (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
      nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ P
  hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
    (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
      nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q'')
  hpair : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q →
    nextUse σ (tᵢ + 1) q'' = some j'' →
    σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧ q'' ∈ schedCache d C₀ σ tᵢ ∧ d tᵢ = q''

/-- iterate_main: induction on sigma.length - t0; case A via iterate_main_exchange (case-one via hAone), case B via hB1/hB2 with t not-in-P from no_nop_at_b2. -/
private lemma iterate_main (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hB1 : ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
      agreeWithFIF st.d C₀ σ t₂ →
      schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
      st.d t₂ ∉ schedCache st.d C₀ σ t₂ →
      σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
      ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1)
    (hB2 : ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
      agreeWithFIF st.d C₀ σ t₂ →
      schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
      st.d t₂ ∈ schedCache st.d C₀ σ t₂ →
      σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
      t₂ ∉ st.P →
      ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1)
    (hAone : ∀ (st : IterateState σ C₀ M) (t : ℕ) (ht : t < σ.length),
      st.hnb ≤ t →
      agreeWithFIF st.d C₀ σ t →
      schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) →
      nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none →
      ∃ st' : IterateState σ C₀ M, st'.t0 = t + 1) :
    ∃ d' : ℕ → Page, ∃ slack' : ℕ,
      agreeWithFIF d' C₀ σ σ.length ∧ schedMisses d' C₀ σ + slack' ≤ M := by
  have hmain : ∀ n : ℕ,
      (∀ m : ℕ, m < n → ∀ (st : IterateState σ C₀ M), σ.length - st.t0 = m →
        ∃ d' slack', agreeWithFIF d' C₀ σ σ.length ∧ schedMisses d' C₀ σ + slack' ≤ M) →
      ∀ (st : IterateState σ C₀ M), σ.length - st.t0 = n →
        ∃ d' slack', agreeWithFIF d' C₀ σ σ.length ∧ schedMisses d' C₀ σ + slack' ≤ M := by
    intro n ih st hlen
    by_cases hfull : agreeWithFIF st.d C₀ σ σ.length
    · refine ⟨st.d, st.slack, hfull, ?_⟩
      exact st.hbook
    · have hnot : ¬ agreeWithFIF st.d C₀ σ σ.length := hfull
      have ht0 : st.t0 ≤ σ.length := by
        by_contra h
        apply hnot
        intro s hs
        exact st.hagree s (by omega)
      rcases exists_first_disagree_after st.d σ C₀ st.t0 ht0 st.hagree hnot with ⟨t, ht₀t, htl, hagt, hnat⟩
      have hdis : schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) := by
        intro hEq
        apply hnat
        intro s hs
        by_cases hs_le : s ≤ t
        · exact hagt s hs_le
        · have hs' : s = t + 1 := by omega
          subst s
          exact hEq
      have hft₂ : σ.getD t 0 ∉ schedCache st.d C₀ σ t := (first_disagree st.d σ C₀ hC₀ htl hagt hdis).1
      by_cases hB : t < st.hnb
      · -- case B:t < hnb,按 d t 是否 resident 分 B2/B1
        by_cases hqin : st.d t ∈ schedCache st.d C₀ σ t
        · -- B2:no_nop_at_b2 给出 t ∉ P
          have ht₂notP : t ∉ st.P := by
            apply no_nop_at_b2 st.d σ C₀ st.Q st.P (t := t)
            · intro tᵢ q'' htq
              have h := st.hpast tᵢ q'' htq
              omega
            · exact st.hP
            · exact st.hcomp
            · exact st.hpair
            · exact htl
            · exact hqin
          rcases hB2 st t htl hB hagt hdis hqin hft₂ ht₂notP with ⟨st', ht0'⟩
          have hmea : σ.length - st'.t0 < n := by
            rw [ht0']
            omega
          rcases ih (σ.length - st'.t0) hmea st' rfl with ⟨d', slack', hagree', hbook'⟩
          exact ⟨d', slack', hagree', hbook'⟩
        · -- B1:no-op 修复
          rcases hB1 st t htl hB hagt hdis hqin hft₂ with ⟨st', ht0'⟩
          have hmea : σ.length - st'.t0 < n := by
            rw [ht0']
            omega
          rcases ih (σ.length - st'.t0) hmea st' rfl with ⟨d', slack', hagree', hbook'⟩
          exact ⟨d', slack', hagree', hbook'⟩
      · -- case A:hnb ≤ t,交换;q' 活则窗口重置,q' 死由 hAone 供应
        have hnb_le : st.hnb ≤ t := by omega
        have hdred_t : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache st.d C₀ σ s → st.d s ∈ schedCache st.d C₀ σ s := by
          intro s hs hf
          exact st.hdred s (by omega) hf
        rcases iterate_main_exchange st.d σ C₀ hC₀ htl hagt hdis hdred_t st.slack with ⟨slack', hagreeE, hbookE, hredE⟩
        let q : Page := st.d t
        let q' : Page := fifoSchedule σ C₀ t
        let e : ℕ → Page := exchangeSchedule st.d t q q' σ C₀
        cases hnext : nextUse σ (t + 1) q' with
        | some j' =>
            have hqin_t : q ∈ schedCache st.d C₀ σ t := by
              dsimp [q]
              exact hdred_t t le_rfl hft₂
            have hqq' : q ≠ q' := by
              intro hqq
              exact (first_disagree st.d σ C₀ hC₀ htl hagt hdis).2.1 (by simpa [q, q', hqq])
            have hfifo2 : nextUse σ (t + 1) q' = none ∨
                ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' := by
              apply fifo_nextUse_order σ (schedCache st.d C₀ σ t) t q' q
              · exact fifo_evict_eq_farthest st.d σ C₀ hagt
              · exact hqin_t
              · exact hqq'
            rcases hfifo2 with hnone2 | ⟨j₀, j₀'', hj₀, hj₀'', hjlt⟩
            · exfalso
              rw [hnext] at hnone2
              cases hnone2
            · have hq₀'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j' → σ.getD k 0 ≠ q' := by
                intro k hk1 hk2
                exact getD_ne_nextUse (k := k) hnext (by omega) (by omega)
              have hred' : ∀ s, max st.hnb (t + 1 + j' + 1) ≤ s →
                  σ.getD s 0 ∉ schedCache e C₀ σ s → e s ∈ schedCache e C₀ σ s := by
                intro s hs hFault
                have hs' : t + 1 + j' < s := by
                  have hle := le_of_max_le_right hs
                  omega
                exact hredE j' hnext (s := s) hs' hFault
              have hwin_inv' : ∀ (d_pre' : ℕ → Page) (t₀' : ℕ) (q₀'' q₀''' : Page) (j₀'' j₀''' : ℕ),
                  some (st.d, t, q, q', j₀, j') = some (d_pre', t₀', q₀'', q₀''', j₀'', j₀''') →
                  t₀' < t + 1 ∧ d_pre' t₀' = q₀'' ∧ q₀'' ≠ q₀''' ∧
                  (∀ s, t₀' ≤ s → σ.getD s 0 ∉ schedCache d_pre' C₀ σ s → d_pre' s ∈ schedCache d_pre' C₀ σ s) ∧
                  σ.getD t₀' 0 ∉ schedCache d_pre' C₀ σ t₀' ∧ q₀''' ∈ schedCache d_pre' C₀ σ t₀' ∧
                  nextUse σ (t₀' + 1) q₀'' = some j₀'' ∧
                  (∀ k, t₀' + 1 ≤ k → k < t₀' + 1 + j₀'' → σ.getD k 0 ≠ q₀''') ∧
                  nextUse σ (t₀' + 1) q₀''' = some j₀''' := by
                intro d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq
                rcases hEq with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
                refine ⟨by omega, rfl, hqq', ?_, hft₂, ?_, hj₀, ?_, hnext⟩
                · intro s hs hf
                  exact st.hdred s (by omega) hf
                · exact (first_disagree st.d σ C₀ hC₀ htl hagt hdis).2.2
                · intro k hk1 hk2
                  have hjlt' : j₀ < j' := by
                    have hj₀''eq : j₀'' = j' := Option.some.inj (hj₀''.symm.trans hnext)
                    omega
                  exact getD_ne_nextUse (k := k) hnext (by omega) (by omega)
              have hbook' : schedMisses e C₀ σ + slack' ≤ M := by
                dsimp [e, q, q']
                exact le_trans hbookE st.hbook
              have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange (some (st.d, t, q, q', j₀, j')) e σ C₀) C₀ σ s \
                  schedCache e C₀ σ s ⊆ (∅ : Finset (ℕ × Page)).image Prod.snd := by
                intro s hs
                dsimp [e, windowExchange]
                simp
              have hd_eq' : ∀ s, s ∉ (∅ : Finset ℕ) → e s = windowExchange (some (st.d, t, q, q', j₀, j')) e σ C₀ s := by
                intro s hs
                rfl
              have hpast' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) → tᵢ < t + 1 := by
                intro tᵢ q'' h
                simp at h
              have hQ' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
                  nextUse σ (tᵢ + 1) q'' = none ∨ ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t + 1 < tᵢ + 1 + j'' := by
                intro tᵢ q'' h
                simp at h
              have hP' : ∀ s, s ∈ (∅ : Finset ℕ) →
                  (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
                  (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
                    nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') := by
                intro s h
                simp at h
              have hcomp' : ∀ s, s ∈ (∅ : Finset ℕ) →
                  (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ ∧ e s = q'') ∨
                  (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
                    nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ e s = q'') := by
                intro s h
                simp at h
              have hpair' : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
                  nextUse σ (tᵢ + 1) q'' = some j'' →
                  σ.getD tᵢ 0 ∉ schedCache e C₀ σ tᵢ ∧ q'' ∈ schedCache e C₀ σ tᵢ ∧ e tᵢ = q'' := by
                intro tᵢ q'' j'' h
                simp at h
              have hQfifo' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
                  q'' = fifoSchedule σ C₀ tᵢ := by
                intro tᵢ q'' h
                simp at h
              have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
                  (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
                    nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ (∅ : Finset ℕ) := by
                intro s h
                rcases h with ⟨tᵢ, q'', htq, hteq⟩ | ⟨tᵢ, q'', j'', htq, hnext, hteq⟩
                · simp at htq
                · simp at htq
              let st' : IterateState σ C₀ M := ⟨e, t + 1, slack', max st.hnb (t + 1 + j' + 1), ∅, ∅,
                some (st.d, t, q, q', j₀, j'), hwin_inv', hagreeE, hbook', hchain', hd_eq', hred',
                hpast', hQ', hQfifo', hP', hP_in', hcomp', hpair'⟩
              have hmea : σ.length - st'.t0 < n := by
                dsimp [st']
                omega
              rcases ih (σ.length - st'.t0) hmea st' rfl with ⟨d', slack', hagree', hbook'⟩
              exact ⟨d', slack', hagree', hbook'⟩
        | none =>
            have hnb_le : st.hnb ≤ t := by omega
            rcases hAone st t htl hnb_le hagt hdis (by simpa [q'] using hnext) with ⟨st', ht0'⟩
            have hmea : σ.length - st'.t0 < n := by
              rw [ht0']
              omega
            rcases ih (σ.length - st'.t0) hmea st' rfl with ⟨d', slack', hagree', hbook'⟩
            exact ⟨d', slack', hagree', hbook'⟩
  exact Nat.strong_induction_on (p := fun n : ℕ => ∀ (st : IterateState σ C₀ M), σ.length - st.t0 = n →
      ∃ d' slack', agreeWithFIF d' C₀ σ σ.length ∧ schedMisses d' C₀ σ + slack' ≤ M)
    (σ.length - st.t0) hmain st rfl

  /-- fifo_optimal: CLRS Theorem 15.5 via iterate_main from the initial state (d0, t0=0, slack=0, hnb=0, Q=P=empty, win=none); the hB1/hB2/hAone supplies are hypotheses. -/
  private lemma fifo_optimal (π : Policy) (C₀ : Finset Page) (σ : List Page)
      (hC₀ : C₀.Nonempty)
      (hB1 : ∀ (M : ℕ) (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
        agreeWithFIF st.d C₀ σ t₂ →
        schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
        st.d t₂ ∉ schedCache st.d C₀ σ t₂ →
        σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
        ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1)
      (hB2 : ∀ (M : ℕ) (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
        agreeWithFIF st.d C₀ σ t₂ →
        schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
        st.d t₂ ∈ schedCache st.d C₀ σ t₂ →
        σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
        t₂ ∉ st.P →
        ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1)
      (hAone : ∀ (M : ℕ) (st : IterateState σ C₀ M) (t : ℕ) (ht : t < σ.length),
        st.hnb ≤ t →
        agreeWithFIF st.d C₀ σ t →
        schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) →
        nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none →
        ∃ st' : IterateState σ C₀ M, st'.t0 = t + 1) :
      misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ := by
    let d₀ : ℕ → Page := policySchedule π C₀ σ
    let M : ℕ := schedMisses d₀ C₀ σ
    have hwin_inv₀ : ∀ (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ),
        none = some (d_pre, t₀, q₀, q₀', j₀, j₀') →
        t₀ < 0 ∧ d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
        (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
        σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
        nextUse σ (t₀ + 1) q₀ = some j₀ ∧
        (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
        nextUse σ (t₀ + 1) q₀' = some j₀' := by
      intro d_pre t₀ q₀ q₀' j₀ j₀' hEq
      cases hEq
    have hagree₀ : agreeWithFIF d₀ C₀ σ 0 := by
      intro s hs
      have hs0 : s = 0 := by omega
      subst s
      rfl
    have hbook₀ : schedMisses d₀ C₀ σ + 0 ≤ M := by rfl
    have hchain₀ : ∀ s, s ≤ σ.length → schedCache (windowExchange none d₀ σ C₀) C₀ σ s \
        schedCache d₀ C₀ σ s ⊆ (∅ : Finset (ℕ × Page)).image Prod.snd := by
      intro s hs
      simp [windowExchange]
    have hd_eq₀ : ∀ s, s ∉ (∅ : Finset ℕ) → d₀ s = windowExchange none d₀ σ C₀ s := by
      intro s hs
      rfl
    have hdred₀ : ∀ s, 0 ≤ s → σ.getD s 0 ∉ schedCache d₀ C₀ σ s → d₀ s ∈ schedCache d₀ C₀ σ s := by
      intro s hs hf
      dsimp [d₀, policySchedule]
      rw [schedCache_policySchedule]
      exact π.evict_mem s (cacheSeq π C₀ σ s) (σ.getD s 0)
        (by simpa [d₀, schedCache_policySchedule] using hf) (cacheSeq_nonempty π C₀ σ s hC₀)
    have hpast₀ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) → tᵢ < 0 := by
      intro tᵢ q'' h
      simp at h
    have hQ₀ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
        nextUse σ (tᵢ + 1) q'' = none ∨ ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ 0 < tᵢ + 1 + j'' := by
      intro tᵢ q'' h
      simp at h
    have hQfifo₀ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
        q'' = fifoSchedule σ C₀ tᵢ := by
      intro tᵢ q'' h
      simp at h
    have hP_in₀ : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
        (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
          nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ (∅ : Finset ℕ) := by
      intro s h
      rcases h with ⟨tᵢ, q'', htq, hteq⟩ | ⟨tᵢ, q'', j'', htq, hnext, hteq⟩
      · simp at htq
      · simp at htq
    have hP₀ : ∀ s, s ∈ (∅ : Finset ℕ) →
        (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
        (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
          nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') := by
      intro s h
      simp at h
    have hcomp₀ : ∀ s, s ∈ (∅ : Finset ℕ) →
        (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ ∧ d₀ s = q'') ∨
        (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
          nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d₀ s = q'') := by
      intro s h
      simp at h
    have hpair₀ : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
        nextUse σ (tᵢ + 1) q'' = some j'' →
        σ.getD tᵢ 0 ∉ schedCache d₀ C₀ σ tᵢ ∧ q'' ∈ schedCache d₀ C₀ σ tᵢ ∧ d₀ tᵢ = q'' := by
      intro tᵢ q'' j'' h
      simp at h
    let st₀ : IterateState σ C₀ M :=
      ⟨d₀, 0, 0, 0, ∅, ∅, none, hwin_inv₀, hagree₀, hbook₀, hchain₀, hd_eq₀, hdred₀,
        hpast₀, hQ₀, hQfifo₀, hP₀, hP_in₀, hcomp₀, hpair₀⟩
    rcases iterate_main σ C₀ hC₀ M st₀ (hB1 M) (hB2 M) (hAone M) with ⟨d', slack', hagree', hbook'⟩
    have hmiss_eq : schedMisses d' C₀ σ = schedMisses (fifoSchedule σ C₀) C₀ σ :=
      schedMisses_eq_of_agree d' σ C₀ hagree'
    have hle : schedMisses (fifoSchedule σ C₀) C₀ σ ≤ M := by
      rw [← hmiss_eq]
      omega
    calc
      misses (fifoPolicy σ) C₀ σ = schedMisses (policySchedule (fifoPolicy σ) C₀ σ) C₀ σ :=
        (schedMisses_policySchedule (fifoPolicy σ) C₀ σ).symm
      _ = schedMisses (fifoSchedule σ C₀) C₀ σ := by rfl
      _ ≤ M := hle
      _ = schedMisses d₀ C₀ σ := rfl
      _ = schedMisses (policySchedule π C₀ σ) C₀ σ := rfl
      _ = misses π C₀ σ := schedMisses_policySchedule π C₀ σ

  end Caching

  end CLRS
