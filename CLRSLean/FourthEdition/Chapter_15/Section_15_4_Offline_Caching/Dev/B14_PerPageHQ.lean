import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B13_PerPageCredit

/-
# Dev B14: the per-page credit invariant — hQ replacement

The state's hQ field over the full-history Q is empirically false
(DESIGN.md "hQ-extension blocker"): a pair whose nop has passed
(`nᵢ ≤ t₂+1` at a case-B step) can never satisfy `t₂+1 < nᵢ` in the
new state — 10236 B1 + 688 B2 steps have an old pair with `nᵢ ≤ t₂`,
212 B1 + 312 B2 steps have `nᵢ = t₂+1`, and 988 B2 steps are reached
from a state whose hQ is already broken.  Pruning broken pairs does not
work (the reverse-diff chain `E − D ⊆ Q.image` needs the full page
history).

What does hold (verified 2026-08-12, exact-iteration search): at every
B2 disagreement `σ[t]` is never the page of any past pair (0 of 55188),
and for an alive pair whose nop has passed, the page stays in the
current cache (`p ∈ D_s` for `nₗ < s` — the "page-stays" mechanism,
684/688; the 4 exceptions have a later dead pair with the same page, so
the page's LAST pair is dead and the hQ's dead disjunct applies).

This file formalizes the per-page credit invariant as the hQ
replacement — the DESIGN's option (b) "the consumers restated to take
the hQ at the consulted pair only", in the per-page form:

- `b2_ehit_ne_per_page`: the per-page consumer — `σ[t] ∉ Q.image` given
  the per-page hQ (`dead ∨ t < nᵢ ∨ credited q''`) and the exclusion
  (credited pages stay in the cache at `t`);
- `last_pair_page_stays`: the page-stays mechanism — for the last pair
  with page `p`, after its nop, `p` stays in the cache — the
  `credited → p ∈ cache` supply (the off-`P` evictions excluded by the
  `hexcl` premise — the exchange's branch analysis);
- `HQPerPageHyp` / `creditedPage`: the assembly's per-page hQ
  hypothesis form.

The per-page credit marks the alive pairs whose nop has passed; the
dead pairs keep the hQ's dead disjunct.  The extension's boundary case
(the new pair with `nᵢ = t₂+1`, the "0 < j''" boundary) is covered by
crediting the new pair's page.

Main results:

- `b2_ehit_ne_per_page`: the per-page hQ consumer
- `last_pair_page_stays`: the page-stays mechanism (the exclusion's
  supply)
- `HQPerPageHyp` / `creditedPage`: the per-page hQ hypothesis form
-/

namespace CLRS

namespace Caching

open Finset

/-- The per-page hQ consumer: at a B2 disagreement `t`, the request
`σ[t]` is not the page of any past pair — given the per-page hQ (each
pair is dead, or not-yet-requested, or its page is credited) and the
exclusion that credited pages stay in the cache at `t` (the B2 fault
`hft`).  This replaces `b2_ehit_ne`'s full-history hQ premise with the
consulted-pair form — the full-history field is empirically false
(DESIGN.md "hQ-extension blocker"). -/
lemma b2_ehit_ne_per_page (σ : List Page) (d : ℕ → Page) (C₀ : Finset Page)
    {t : ℕ} (ht : t < σ.length)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (Q : Finset (ℕ × Page))
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t)
    (credited : Page → Prop)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        (∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t < tᵢ + 1 + j'') ∨
        credited q'')
    (hexcl : ∀ p, credited p → p ∈ schedCache d C₀ σ t) :
    σ.getD t 0 ∉ Q.image Prod.snd := by
  intro hsigQ
  rcases Finset.mem_image.mp hsigQ with ⟨⟨tᵢ, q''⟩, htq, hsigq⟩
  have htlt : tᵢ < t := hpast tᵢ q'' htq
  rcases hQ tᵢ q'' htq with hdead | hrest
  · -- 死页:σ[t] = q'' 与 `q''` 在 tᵢ 之后永不请求矛盾
    exact getD_ne_of_nextUse_none σ hdead (by omega) ht hsigq.symm
  · rcases hrest with ⟨j'', hnext, htltJ⟩ | hcred
    · -- 未请求:t < J''ᵢ 处请求 σ[t] = q'' 与首次请求在 J''ᵢ 矛盾
      exact getD_ne_nextUse (k := t) hnext (by omega) htltJ hsigq.symm
    · -- credited:页仍在 cache 中,与 B2 缺页 `hft` 矛盾
      exact hft (hsigq ▸ hexcl q'' hcred)

/-- 页面停留机制:窗口内,页 `p` 的最后一个对(`tₗ` 之后无对再以 `p` 为页,
`hlast`)在其 nop `nₗ = tₗ+1+j''ₗ` 之后留在当前 cache 中。归纳从 `nₗ+1`
起:命中不改 cache;缺页处逐出值不是 `p` —— P 位置的逐出是某对的页
(`hcomp`),`tᵢ` 位置由 `hlast` 排除 `p`,nop 位置 `σ[nᵢ] = q''` 的
insert-erase 是 no-op(页留驻);off-P 位置由 `hexcl` 前提排除(交换的
逐出分析,见 DESIGN "hQ-extension blocker" 的交换分支)。 -/
lemma last_pair_page_stays (σ : List Page) (C₀ : Finset Page)
    (d : ℕ → Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    {tₗ : ℕ} {p : Page} {j''ₗ : ℕ}
    (hj''ₗ : nextUse σ (tₗ + 1) p = some j''ₗ)
    (hlast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = p → tᵢ ≤ tₗ)
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q''))
    (hexcl : ∀ s, tₗ < s → s ≤ σ.length → s ∉ P → d s ≠ p) :
    ∀ s, tₗ + 1 + j''ₗ < s → s ≤ σ.length → p ∈ schedCache d C₀ σ s := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs1 hs2
      by_cases hs_eq : s = tₗ + 1 + j''ₗ
      · -- base:s+1 = nₗ+1 —— 请求 σ[nₗ] = p 在 nₗ 加载(命中或缺页都含 p)
        subst s
        have hget : σ.getD (tₗ + 1 + j''ₗ) 0 = p := getD_eq_nextUse hj''ₗ
        rw [schedCache]
        by_cases hr : σ.getD (tₗ + 1 + j''ₗ) 0 ∈ schedCache d C₀ σ (tₗ + 1 + j''ₗ)
        · rw [if_pos hr]
          exact (hget.symm ▸ hr)
        · rw [if_neg hr]
          rw [Finset.mem_insert]
          left
          exact hget.symm
      · have hs1' : tₗ + 1 + j''ₗ < s := by omega
        have hpin : p ∈ schedCache d C₀ σ s := ih hs1' (by omega)
        rw [schedCache]
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · -- 命中:cache 不变
          rw [if_pos hr]
          exact hpin
        · -- 缺页:逐出 `d s`,证明 `d s ≠ p` 或 no-op
          rw [if_neg hr]
          rw [Finset.mem_insert]
          by_cases hsp : s ∈ P
          · -- P 位置:逐出某对的页
            rcases hcomp s hsp with ⟨tᵢ, q'', htq, hteq, hdval⟩ | ⟨tᵢ, q'', j'', htq, hnext, hteq, hdval⟩
            · -- tᵢ 位置:该对在 `tₗ` 之后,`hlast` 给出 `q'' ≠ p`
              right
              rw [Finset.mem_erase]
              exact ⟨(by
                intro h
                have hpq : q'' = p := hdval.symm.trans h.symm
                have hle := hlast tᵢ q'' htq hpq
                have hgt : tₗ < tᵢ := by
                  rw [← hteq]
                  omega
                omega), hpin⟩
            · -- nop 位置:请求 σ[s] = q'',insert-erase 是 no-op(页留驻)
              have hget : σ.getD s 0 = q'' := by
                rw [hteq]
                exact getD_eq_nextUse hnext
              by_cases hpq : p = q''
              · -- p = q'':请求即 p,insert 直接给出
                left
                rw [hget]
                exact hpq
              · right
                rw [Finset.mem_erase]
                exact ⟨(by
                  intro h
                  exact hpq (hdval.symm.trans h.symm).symm), hpin⟩
          · -- off-P:hexcl 前提排除逐出 `p`
            right
            rw [Finset.mem_erase]
            exact ⟨(by
              intro h
              exact hexcl s (by omega) (by omega) hsp h.symm), hpin⟩

/-- 逐页 credit 谓词:页 `q''` 被 credit —— 存在以 `q''` 为页的活对,其
nop 已过(`tᵢ + 1 + j'' ≤ t₂ + 1`,包括新对 `nᵢ = t₂+1` 的边界情形)。
`b2_ehit_ne_per_page` 的 `hexcl` 由 `last_pair_page_stays` 供应
(credited 页仍在 cache 中)。 -/
def creditedPage (σ : List Page) (Q : Finset (ℕ × Page)) (t₂ : ℕ) (q'' : Page) : Prop :=
  ∃ (tᵢ : ℕ) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
    nextUse σ (tᵢ + 1) q'' = some j'' ∧ tᵢ + 1 + j'' ≤ t₂ + 1

/-- 逐页 hQ 前提:装配层以逐页 credit 取代全历史 hQ —— 新状态 `Q'` 中每
个对要么死、要么未请求(`t₂+1 < nᵢ`)、要么其页被 credit(页仍在 cache
的排除由 `b2_ehit_ne_per_page` 的 `hexcl` 给出)。旧对沿用 strengthened
界 `t₂ < nᵢ`(由 `b2_hQ_supply_old` 的 `past_pair_first_request_after`
供应);新对的 `nᵢ = t₂+1` 边界情形由 credit 覆盖。 -/
def HQPerPageHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ),
    (∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'') ∧
    (∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        (∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'') ∨
        creditedPage σ st.Q t₂ q'')

end Caching

end CLRS
