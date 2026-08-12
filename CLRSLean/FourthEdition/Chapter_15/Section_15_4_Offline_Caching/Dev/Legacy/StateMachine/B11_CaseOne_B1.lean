import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.Legacy.StateMachine.B9_Assembly

/-
# Dev B11: the case-one no-window B1 step

After a case-one exchange, the next disagreement (when one exists) lands
exactly on the branch-1 spot `s₁` (DESIGN.md "Case-one branch-1
verified"): the exchange evicts `q'` there as a no-op, so its cache
grows and disagrees with FIF at `s₁+1`.  With `hnb' = σ.length + 2` the
dispatch is case B — but the case-one state has `win = none`.

This file supplies the no-window B1 step: the repair at `t₂` evicts the
FIF page `q''` (resident by agreement), restoring agreement at `t₂+1`.
The window machinery is vacuous (`windowExchange none d = d`); the
reverse diff `E_s − Ŝ_s ⊆ q''` on `(t₂, J''']` replaces the window's
`repair_diff_noop_window`.  The step's `0 < j'''` clause for the new
pair is a premise (the DESIGN's "0 < j''" boundary case).

- `caseone_b1_reverse_diff`: the paired diff `E_s − Ŝ_s ⊆ q''` and
  subset `Ŝ_s ⊆ E_s` on `(t₂, J''']` — the repair's real eviction of
  `q''` at `t₂` is the only difference; both caches evolve identically
  afterwards (evictions agree off `t₂, J'''` and the requests are not
  `q''` before `J'''`).
- `caseone_b1_misses_le`: `schedMisses r ≤ schedMisses d + bad` — the
  pointwise `rF ≤ eF` off `J'''` (the reverse diff + the
  request-exclusion), the `J'''` handling `rF = 1` with `eF + bad = 1`.

Both lemmas now kernel-check (2026-08-12): the subset step's rewrites
order the r-cache if before the d-cache facts, and the `hdiff`/`hsup`
calls pass `hq''` instead of `rfl` (the caller's `q''` is not defeq).
-/

namespace CLRS

namespace Caching

open Finset

/-- 无窗口 B1 的配对反向差:`(t₂, J'''] 内`
`E_s − Ŝ_s ⊆ q''` 且 `Ŝ_s ⊆ E_s` —— 修复在 `t₂` 真逐出 `q''`(FIF 的页)
是唯一差;此后二者缓存同步演化(逐出一致 off `t₂, J'''` 两点,请求 `σ s ≠ q''`
⟹ 同 hit/fault)。第二方向(Ŝ ⊆ E)供步骤的命中同步。 -/
lemma caseone_b1_reverse_diff (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length)
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : d t₂ ∉ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) q'' = some j''') :
    ∀ s, t₂ < s → s ≤ t₂ + 1 + j''' →
      schedCache d C₀ σ s \ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s ⊆ ({q''} : Finset Page) ∧
      schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s ⊆ schedCache d C₀ σ s := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs1 hs2
      by_cases hs_eq : s = t₂
      · -- base:s+1 = t₂+1 —— 修复真逐出 q'',`d` 逐出 d t₂(no-op)
        subst s
        have hce_t : schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ t₂ =
            schedCache d C₀ σ t₂ := by
          exact schedCache_repairSchedule_eq_e d t₂ q'' (t₂ + 1 + j''') (by omega) σ C₀ le_rfl
        have hS : schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ (t₂ + 1) =
            insert (σ.getD t₂ 0) ((schedCache d C₀ σ t₂).erase q'') := by
          rw [schedCache]
          rw [hce_t, if_neg hftd, repairSchedule_at_t d t₂ q'' (t₂ + 1 + j''')]
        have hD : schedCache d C₀ σ (t₂ + 1) =
            insert (σ.getD t₂ 0) ((schedCache d C₀ σ t₂).erase (d t₂)) := by
          rw [schedCache]
          rw [if_neg hftd]
        constructor
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_singleton]
          rcases Finset.mem_insert.mp (by rw [← hD]; exact hx.1) with hxr | hxE
          · exfalso
            exact hx.2 (by rw [hS, hxr]; exact Finset.mem_insert_self _ _)
          · have hxne_d : x ≠ d t₂ := (Finset.mem_erase.mp hxE).1
            have hxin : x ∈ schedCache d C₀ σ t₂ := (Finset.mem_erase.mp hxE).2
            by_cases hxq : x = q''
            · exact hxq
            · exfalso
              exact hx.2 (by rw [hS]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxq, hxin⟩)))
        · intro x hx
          rw [hS] at hx
          rw [hD]
          rw [Finset.mem_insert]
          rcases Finset.mem_insert.mp hx with hxr | hxE
          · exact Or.inl hxr
          · right
            rw [Finset.mem_erase]
            exact ⟨(by intro hxd; exact hnoop (hxd ▸ (Finset.mem_erase.mp hxE).2)),
                   (Finset.mem_erase.mp hxE).2⟩
      · -- step:请求 σ s ≠ q''(s < J'''),逐出一致(off {t₂, J'''})
        have hs1' : t₂ < s := by omega
        have hneq : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj''' (by omega) (by omega)
        have hihd : schedCache d C₀ σ s \ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s ⊆ ({q''} : Finset Page) := (ih hs1' (by omega)).1
        have hihs : schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s ⊆ schedCache d C₀ σ s := (ih hs1' (by omega)).2
        have hrs : repairSchedule d t₂ q'' (t₂ + 1 + j''') s = d s := by
          simp [repairSchedule, show s ≠ t₂ by (intro h; exact hs_eq h),
                show s ≠ t₂ + 1 + j''' by omega]
        -- 命中同步:σ s ∈ Ŝ_s ⟺ σ s ∈ E_s
        have hsync_f : σ.getD s 0 ∈ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s →
            σ.getD s 0 ∈ schedCache d C₀ σ s := fun h => hihs h
        have hsync_r : σ.getD s 0 ∈ schedCache d C₀ σ s →
            σ.getD s 0 ∈ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s := by
          intro hd
          by_contra hr
          have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s := by
            rw [Finset.mem_sdiff]
            exact ⟨hd, hr⟩
          have hq'eq : σ.getD s 0 = q'' := Finset.mem_singleton.mp (hihd hmem)
          exact hneq hq'eq
        constructor
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_singleton]
          simp only [schedCache] at hx
          by_cases hr : σ.getD s 0 ∈ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s
          · have hd : σ.getD s 0 ∈ schedCache d C₀ σ s := hsync_f hr
            rw [if_pos hd, if_pos hr] at hx
            exact Finset.mem_singleton.mp (hihd (Finset.mem_sdiff.mpr hx))
          · have hnd : σ.getD s 0 ∉ schedCache d C₀ σ s := by
              intro hd
              exact hr (hsync_r hd)
            rw [if_neg hnd, if_neg hr] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr' | hxE
            · exfalso
              exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr'))
            · have hxne_d : x ≠ d s := (Finset.mem_erase.mp hxE).1
              have hxin : x ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hxE).2
              have hmem : x ∈ schedCache d C₀ σ s \ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, by
                  intro hxS
                  exact hx.2 (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨(by
                    intro hxr
                    rw [hrs] at hxr
                    exact hxne_d hxr), hxS⟩)))⟩
              exact Finset.mem_singleton.mp (hihd hmem)
        · intro x hx
          simp only [schedCache] at hx
          rw [schedCache]
          by_cases hr : σ.getD s 0 ∈ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s
          · have hd : σ.getD s 0 ∈ schedCache d C₀ σ s := hsync_f hr
            rw [if_pos hr] at hx
            rw [if_pos hd]
            exact hihs hx
          · have hnd : σ.getD s 0 ∉ schedCache d C₀ σ s := by
              intro hd
              exact hr (hsync_r hd)
            rw [if_neg hr] at hx
            rw [if_neg hnd]
            rcases Finset.mem_insert.mp hx with hxr' | hxE
            · rw [Finset.mem_insert]
              exact Or.inl hxr'
            · have hxne_r : x ≠ repairSchedule d t₂ q'' (t₂ + 1 + j''') s := (Finset.mem_erase.mp hxE).1
              have hxin : x ∈ schedCache (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ s := (Finset.mem_erase.mp hxE).2
              rw [Finset.mem_insert]
              right
              rw [Finset.mem_erase]
              constructor
              · intro hxd
                rw [← hrs] at hxd
                exact hxne_r hxd
              · exact hihs hxin

/-- 无窗口 B1 的 miss 记账:`schedMisses r ≤ schedMisses d + bad`(坏事件
`σ[J'''] ∈ D_{J'''}` 处 `rF = 1` 而 `dF = 1 − bad`;其余位置由反向差 +
超集给出 `rF ≤ dF`)。 -/
lemma caseone_b1_misses_le (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length)
    (hagree : agreeWithFIF d C₀ σ t₂)
    (hdis : schedCache d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : d t₂ ∉ schedCache d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) q'' = some j''') :
    schedMisses (repairSchedule d t₂ q'' (t₂ + 1 + j''')) C₀ σ ≤
      schedMisses d C₀ σ +
        if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''') then 1 else 0 := by
  let r : ℕ → Page := repairSchedule d t₂ q'' (t₂ + 1 + j''')
  let dF : ℕ → ℕ := schedFaultAt d C₀ σ
  let rF : ℕ → ℕ := schedFaultAt r C₀ σ
  have hq''res : q'' ∈ schedCache d C₀ σ t₂ := by
    have hfd := first_disagree d σ C₀ hC₀ ht₂ hagree hdis
    exact hq''.symm ▸ hfd.2.2
  have hq''notS : ∀ s, t₂ < s → s ≤ t₂ + 1 + j''' → q'' ∉ schedCache r C₀ σ s := by
    intro s hs1 hs2
    exact repair_q''_absent d σ C₀ (q'' := q'') hftd hq''res hq'' hj''' s hs1 hs2
  have hdiff := caseone_b1_reverse_diff d σ C₀ hC₀ ht₂ hagree hdis hnoop hftd hq'' hj'''
  have hpoint_le : ∀ s, s < σ.length → s ≠ t₂ + 1 + j''' →
      schedFaultAt r C₀ σ s ≤ schedFaultAt d C₀ σ s := by
    intro s hs hsne
    simp only [r, schedFaultAt]
    by_cases hs_le_t : s ≤ t₂
    · rw [schedCache_repairSchedule_eq_e d t₂ q'' (t₂ + 1 + j''') (by omega) σ C₀ hs_le_t]
    · have hs1 : t₂ < s := by omega
      by_cases hsJ : s ≤ t₂ + 1 + j'''
      · -- (t₂, J''']:反向差 + 请求排除 ⟹ 同 hit/fault
        have hdiff' : schedCache d C₀ σ s \ schedCache r C₀ σ s ⊆ ({q''} : Finset Page) := (hdiff s hs1 hsJ).1
        have hneq : σ.getD s 0 ≠ q'' := by
          rcases lt_or_eq_of_le hsJ with hslt | hseq
          · exact getD_ne_nextUse (k := s) hj''' (by omega) (by omega)
          · rw [hseq] at hsne
            exact (hsne rfl).elim
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · have hr' : σ.getD s 0 ∈ schedCache r C₀ σ s := by
            by_contra h
            have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨hr, h⟩
            have hq'eq : σ.getD s 0 = q'' := Finset.mem_singleton.mp (hdiff' hmem)
            exact hneq hq'eq
          rw [if_pos hr, if_pos hr']
        · rw [if_neg hr]
          by_cases hr' : σ.getD s 0 ∈ schedCache r C₀ σ s
          · rw [if_pos hr']
            omega
          · rw [if_neg hr']
      · -- s > J''':E ⊆ Ŝ
        have hsJ' : t₂ + 1 + j''' < s := by omega
        have hsup : schedCache d C₀ σ s ⊆ schedCache r C₀ σ s := by
          exact repairSchedule_superset d σ C₀ hC₀ ht₂ hagree hdis hnoop hq'' hj''' (s := s) hsJ'
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · rw [if_pos hr]
          rw [if_pos (hsup hr)]
        · rw [if_neg hr]
          by_cases hr' : σ.getD s 0 ∈ schedCache r C₀ σ s
          · rw [if_pos hr']
            omega
          · rw [if_neg hr']
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
    exact Finset.sum_le_sum (fun s hs => hpoint_le s
      (Finset.mem_range.mp (Finset.mem_erase.mp hs).2) (Finset.mem_erase.mp hs).1)
  by_cases hbad : σ.getD (t₂ + 1 + j''') 0 ∈ schedCache d C₀ σ (t₂ + 1 + j''')
  · rw [if_pos hbad]
    have hdFJ : schedFaultAt d C₀ σ (t₂ + 1 + j''') = 0 := by
      unfold schedFaultAt
      rw [hsig]
      rw [if_pos (by rwa [← hsig])]
    rw [← hsum_erase_r]
    have h' := hsum_erase_d
    rw [hdFJ] at h'
    omega
  · rw [if_neg hbad]
    have hdFJ : schedFaultAt d C₀ σ (t₂ + 1 + j''') = 1 := by
      unfold schedFaultAt
      rw [hsig]
      rw [if_neg (by rwa [← hsig])]
    rw [← hsum_erase_r]
    have h' := hsum_erase_d
    rw [hdFJ] at h'
    omega

end Caching

end CLRS
