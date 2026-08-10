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
- `b2_hswap_qp_dead`: same for the `q''`-dead case — `repair_keep_swap_qp_dead`
  (B6), the dead-page repair `repairSchedule e t q'' t` still has the swap
  form at `J` (the good event for `repair_step_swap_qp_dead`)
- `iterate_main_exchange`: the case-A step of `iterate_main` — at the first
  disagreement `t`, the exchange extends agreement to `t + 1`, never
  increases misses (slack `+1` iff the bad event did not occur), and is
  reduced from `J' + 1` when `q'` is requested again

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

end Caching

end CLRS
