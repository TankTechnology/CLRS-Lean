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

end Caching

end CLRS
