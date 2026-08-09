import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B5_Iteration

/-!
# Dev B6: the strong B2 repair (no slack needed)

Development file for the resident (B2) repair step of the `fifo_optimal`
iteration (see `Dev/DESIGN.md`): when `q = e t` is resident at a case-B
position, the repair `r = repairSchedule e t q'' (t+1+j'')` costs **no
slack** — the good event at `J = t+1+j` (the repair hits where `e` faults)
offsets the bad event at `J'' = t+1+j''`.  This is the "strong version" of
`repair_step_swap` (B4), whose only extra hypothesis is the keep-swap form
`Ŝ_J = insert q (E_J − q'')`; `repair_keep_swap` derives that form in the
iteration context (the exchange window), where the multi-set branches can
never evict `q`.

Also: the dead-page sub-cases.  If `q` is never requested again, then so is
`q''` (the FIF choice is the farthest page, and `none` is farthest), and the
repair differs from `e` only on `{q, q''}` — equal miss counts, free.

Main results:

- `getD_ne_of_nextUse_none`: `nextUse σ i p = none` ⟹ no request of `p`
  at or after `i`
- `repair_q_dead_qp_dead`: `nextUse q = none` ⟹ `nextUse q'' = none`
- `repair_cache_diff`: the repair's cache differs from `e`'s by ⊆ `{q, q''}`
  (requests avoid `{q, q''}` — no keep-swap, no reducedness)
- `repair_step_swap_q_dead`: both pages dead ⟹ `schedMisses r ≤ schedMisses e`
  and agreement extends (free)
- `repair_step_swap_strong`: keep-swap form at `J` ⟹ `schedMisses r ≤
  schedMisses e` and agreement extends (no slack)
- `exchange_no_evict_q`: in the exchange window, the exchange never evicts
  `q` on `(t₂, J]` (branch 1 evicts `q₀'`, branches 4-6 evict pages of `C'`,
  branch 5 evicts `d s` — none can be `q`)
- `repair_keep_swap`: the swap form survives to `J` in the exchange window

This file is part of the `fifo_optimal` iteration; it will be merged into
`S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

set_option maxHeartbeats 400000

/-- 若 `nextUse σ i p = none`,则 `i` 之后(在 `σ` 范围内)没有任何请求是 `p`。 -/
lemma getD_ne_of_nextUse_none (σ : List Page) {i p : ℕ}
    (h : nextUse σ i p = none) {s : ℕ} (hs1 : i ≤ s) (hs2 : s < σ.length) :
    σ.getD s 0 ≠ p := by
  intro hsp
  have hnone := (nextUse_eq_none_iff.mp h)
  have hmem : p ∈ σ.drop i := by
    have hslt : s - i < (σ.drop i).length := by
      rw [List.length_drop]
      omega
    have hget : (σ.drop i).getD (s - i) 0 = p := by
      rw [getD_drop σ 0 i (s - i)]
      have hsub : i + (s - i) = s := by omega
      simpa [hsub] using hsp
    have hget' : (σ.drop i)[s - i] = p := by
      rw [← List.getD_eq_getElem (σ.drop i) 0 hslt]
      exact hget
    exact hget' ▸ getElem_mem hslt
  exact hnone p hmem rfl

/-- 若 B2 位置的 `q = e t` 永不再请求,则 FIF 在该处的选择 `q''` 也永不再
请求(`q''` 是最远页,而 `none` 是最远;`farthestInFuture_max`)。 -/
lemma repair_q_dead_qp_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hqdead : nextUse σ (t + 1) (e t) = none) :
    nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none := by
  let q : Page := e t
  have hmax : Farther (nextUse σ (t + 1) (fifoSchedule σ C₀ t)) (nextUse σ (t + 1) q) := by
    rw [fifo_evict_eq_farthest e σ C₀ hagree]
    exact farthestInFuture_max (by simpa [q] using hqin)
  rcases farther_cases hmax with hn | ⟨i, j, hi, hj, hle⟩
  · simpa [q] using hn
  · exfalso
    rw [hqdead] at hj
    contradiction

/-- 死页修复的 cache 差:`r = repairSchedule e t q'' t`(除 `t` 处逐出 `q''`
而非 `q` 外与 `e` 处处相同)与 `e` 的 cache 处处只差 `{q, q''}` 中的页。
需要请求避开 `{q, q''}`(`hdead`),这排除了混合 hit/fault 情形。
不需要 keep-swap、不需要 reducedness。 -/
lemma repair_cache_diff (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : e t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqq'' : q ≠ q'')
    (hdead : ∀ s, t < s → s < σ.length → σ.getD s 0 ∉ ({q, q''} : Finset Page)) :
    ∀ s, s ≤ σ.length →
      (schedCache (repairSchedule e t q'' t) C₀ σ s \ schedCache e C₀ σ s) ⊆
          ({q, q''} : Finset Page) ∧
      (schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' t) C₀ σ s) ⊆
          ({q, q''} : Finset Page) := by
  let r : ℕ → Page := repairSchedule e t q'' t
  have hrt : r t = q'' := by simp [r, repairSchedule]
  have hr_ne : ∀ s, s ≠ t → r s = e s := by
    intro s hs
    simp [r, repairSchedule, hs]
  have hc : ∀ s, s ≤ t → schedCache r C₀ σ s = schedCache e C₀ σ s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
        have hst : s ≤ t := by omega
        have hst' : s ≠ t := by omega
        rw [schedCache, schedCache]
        rw [ih hst]
        rw [show r s = e s by exact hr_ne s hst']
  intro s
  induction s with
  | zero =>
      intro hlen
      constructor <;> intro x hx <;> exfalso <;> simp [schedCache] at hx
  | succ s ih =>
      intro hlen
      have hslt : s < σ.length := by omega
      by_cases hs_le_t : s + 1 ≤ t
      · -- s+1 ≤ t:caches equal
        constructor
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          exfalso
          exact hx.2 (by rw [← hc (s + 1) hs_le_t]; exact hx.1)
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          exfalso
          exact hx.2 (by rw [hc (s + 1) hs_le_t]; exact hx.1)
      · by_cases hs_eq : s = t
        · -- base:s+1 = t+1
          subst s
          have hS : schedCache r C₀ σ (t + 1) = insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q'') := by
            rw [schedCache]
            rw [hc t le_rfl]
            rw [if_neg hft]
            rw [hrt]
          have hE : schedCache e C₀ σ (t + 1) = insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q) := by
            rw [schedCache]
            rw [if_neg hft]
            rw [hq]
          constructor
          · intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_insert]
            rcases Finset.mem_insert.mp (hS ▸ hx.1) with hxr | hxE
            · exfalso
              exact hx.2 (hE ▸ (Finset.mem_insert.mpr (Or.inl hxr)))
            · -- x ∈ (E_t − q'') 且 x ∉ E' ⟹ x = q
              have hxin : x ∈ schedCache e C₀ σ t := (Finset.mem_erase.mp hxE).2
              have hxq : x = q := by
                by_contra hxne
                have hxE' : x ∈ insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q) := by
                  rw [Finset.mem_insert]
                  exact Or.inr (Finset.mem_erase.mpr ⟨hxne, hxin⟩)
                exact hx.2 (hE ▸ hxE')
              left
              exact hxq
          · intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_insert]
            rcases Finset.mem_insert.mp (hE ▸ hx.1) with hxr | hxE
            · exfalso
              exact hx.2 (hS ▸ (Finset.mem_insert.mpr (Or.inl hxr)))
            · -- x ∈ (E_t − q) 且 x ∉ Ŝ' ⟹ x = q''
              have hxin : x ∈ schedCache e C₀ σ t := (Finset.mem_erase.mp hxE).2
              have hxq'' : x = q'' := by
                by_contra hxne
                have hxS' : x ∈ insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q'') := by
                  rw [Finset.mem_insert]
                  exact Or.inr (Finset.mem_erase.mpr ⟨hxne, hxin⟩)
                exact hx.2 (hS ▸ hxS')
              right
              rw [Finset.mem_singleton]
              exact hxq''
        · -- step:s > t
          have hst : t < s := by omega
          have hs_ne : s ≠ t := by omega
          have hmem_eq : (σ.getD s 0 ∈ schedCache r C₀ σ s) ↔
              (σ.getD s 0 ∈ schedCache e C₀ σ s) := by
            constructor
            · intro hr
              by_contra he
              have hmem : σ.getD s 0 ∈ schedCache r C₀ σ s \ schedCache e C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hr, he⟩
              exact hdead s hst hslt ((ih (by omega)).1 hmem)
            · intro he
              by_contra hr
              have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨he, hr⟩
              exact hdead s hst hslt ((ih (by omega)).2 hmem)
          rw [schedCache, schedCache]
          rw [show repairSchedule e t q'' t s = e s by
            unfold repairSchedule
            simp [hs_ne]]
          by_cases hfault : σ.getD s 0 ∈ schedCache e C₀ σ s
          · -- both hit:caches unchanged
            rw [if_pos hfault, if_pos (hmem_eq.mpr hfault)]
            exact ih (by omega)
          · -- both fault
            rw [if_neg hfault, if_neg (by intro hr; exact hfault (hmem_eq.mp hr))]
            constructor
            · -- Ŝ' − E' ⊆ {q,q''}
              intro x hx
              rw [Finset.mem_sdiff] at hx
              rw [Finset.mem_insert]
              rcases Finset.mem_insert.mp hx.1 with hxr | hxS
              · exfalso
                exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
              · -- x ∈ Ŝ_s − e s,x ∉ insert σ[s] (E_s − e s)
                have hxin : x ∈ schedCache r C₀ σ s := (Finset.mem_erase.mp hxS).2
                have hxne : x ≠ e s := (Finset.mem_erase.mp hxS).1
                by_cases hxE : x ∈ schedCache e C₀ σ s
                · -- x ∈ Ŝ ∩ E:x = e s or x ∉ E'(矛盾)⟹ x = e s ⟹ x 被两方逐出?不 — x ≠ e s — 矛盾
                  exfalso
                  -- x ∈ E_s,x ∉ insert σ[s] (E_s − e s) ⟹ x = e s(与 hxne 矛盾)或 x = σ[s](x ∈ E_s,σ[s] ∉ E_s — 矛盾)
                  by_cases hxeq : x = σ.getD s 0
                  · exact hfault (hxeq ▸ hxE)
                  · have hmem' : x ∈ insert (σ.getD s 0) ((schedCache e C₀ σ s).erase (e s)) := by
                      rw [Finset.mem_insert]
                      exact Or.inr (Finset.mem_erase.mpr ⟨hxne, hxE⟩)
                    exact hx.2 hmem'
                · -- x ∈ Ŝ − E ⊆ {q,q''}
                  have hmem : x ∈ schedCache r C₀ σ s \ schedCache e C₀ σ s := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hxin, hxE⟩
                  exact Finset.mem_insert.mp ((ih (by omega)).1 hmem)
            · -- E' − Ŝ' ⊆ {q,q''}
              intro x hx
              rw [Finset.mem_sdiff] at hx
              rw [Finset.mem_insert]
              rcases Finset.mem_insert.mp hx.1 with hxr | hxE
              · exfalso
                exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
              · have hxin : x ∈ schedCache e C₀ σ s := (Finset.mem_erase.mp hxE).2
                have hxne : x ≠ e s := (Finset.mem_erase.mp hxE).1
                by_cases hxS : x ∈ schedCache r C₀ σ s
                · -- x ∈ E ∩ Ŝ ⟹ x = e s 或 σ[s] — 与 hx.2 矛盾
                  exfalso
                  by_cases hxeq : x = σ.getD s 0
                  · exact hx.2 (Finset.mem_insert.mpr (Or.inl hxeq))
                  · have hmem' : x ∈ insert (σ.getD s 0) ((schedCache r C₀ σ s).erase (e s)) := by
                      rw [Finset.mem_insert]
                      exact Or.inr (Finset.mem_erase.mpr ⟨hxne, hxS⟩)
                    exact hx.2 hmem'
                · have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hxin, hxS⟩
                  exact Finset.mem_insert.mp ((ih (by omega)).2 hmem)

/-- B2 且 `q` 永不再请求(`q''` 也随之永不再请求):修复 `r` 与 `e` 的
cache 只差 `{q, q''}`(均为死页),故 miss 数相同,一致性扩展到 `t + 1`。
无需 slack。 -/
lemma repair_step_swap_q_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hqdead : nextUse σ (t + 1) (e t) = none) :
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ ≤ schedMisses e C₀ σ ∧
    agreeWithFIF (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ (t + 1) := by
  let q : Page := e t
  let q'' : Page := fifoSchedule σ C₀ t
  let r : ℕ → Page := repairSchedule e t q'' t
  have hq''dead : nextUse σ (t + 1) q'' = none := repair_q_dead_qp_dead e σ C₀ ht hagree hqin hqdead
  have hqq'' : q ≠ q'' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq
    exact hfd.2.1 (by simpa [q, q'', hqq])
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    exact hfd.1
  have hdead : ∀ s, t < s → s < σ.length → σ.getD s 0 ∉ ({q, q''} : Finset Page) := by
    intro s hst hslt hmem
    rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
    · exact getD_ne_of_nextUse_none σ (by simpa [q] using hqdead) (by omega) hslt hqeq
    · exact getD_ne_of_nextUse_none σ (by simpa [q''] using hq''dead) (by omega) hslt
        (Finset.mem_singleton.mp hq'eq)
  have hdiff := repair_cache_diff e σ C₀ (show e t = q from rfl) rfl hft hqq'' hdead
  have hc : ∀ s, s ≤ t → schedCache r C₀ σ s = schedCache e C₀ σ s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih2 =>
        have hst : s ≤ t := by omega
        have hst' : s ≠ t := by omega
        rw [schedCache, schedCache]
        rw [ih2 hst]
        rw [show r s = e s by
          unfold r repairSchedule
          simp [hst']]
  constructor
  · -- misses:rF = eF pointwise
    have hpoint : ∀ s, s < σ.length → schedFaultAt r C₀ σ s = schedFaultAt e C₀ σ s := by
      intro s hs
      unfold schedFaultAt
      by_cases hs_le_t : s ≤ t
      · -- caches equal
        rw [hc s hs_le_t]
      · -- s > t:σ[s] ∉ {q,q''} ⟹ hit 对齐
        have hst : t < s := by omega
        have hneq_q : σ.getD s 0 ≠ q := by
          intro hq'
          exact hdead s hst hs (Finset.mem_insert.mpr (Or.inl hq'))
        have hneq_q'' : σ.getD s 0 ≠ q'' := by
          intro hq'
          exact hdead s hst hs (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hq')))
        by_cases he : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos he]
          rw [if_pos (by
            by_contra hr
            have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hr⟩
            have hq' := (hdiff s (by omega)).2 hmem
            rcases Finset.mem_insert.mp hq' with hqeq | hq'eq
            · exact hneq_q hqeq
            · exact hneq_q'' (Finset.mem_singleton.mp hq'eq))]
        · rw [if_neg he]
          rw [if_neg (by
            intro hr
            have hmem : σ.getD s 0 ∈ schedCache r C₀ σ s \ schedCache e C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨hr, he⟩
            have hq' := (hdiff s (by omega)).1 hmem
            rcases Finset.mem_insert.mp hq' with hqeq | hq'eq
            · exact hneq_q hqeq
            · exact hneq_q'' (Finset.mem_singleton.mp hq'eq))]
    unfold schedMisses
    rw [Finset.sum_congr rfl (by
      intro s hs
      exact hpoint s (Finset.mem_range.mp hs))]
  · -- agree 到 t+1
    intro s hs
    by_cases hs' : s ≤ t
    · -- s ≤ t:caches equal
      rw [hc s hs']
      exact hagree s hs'
    · have hst : s = t + 1 := by omega
      subst s
      have hq''res : q'' ∈ schedCache e C₀ σ t := by
        have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
        exact hfd.2.2
      have hsig_ne : σ.getD t 0 ≠ q'' := by
        intro hsig
        exact hft (hsig ▸ hq''res)
      have hE : schedCache r C₀ σ (t + 1) = insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q'') := by
        rw [schedCache]
        rw [show schedCache r C₀ σ t = schedCache e C₀ σ t by
          exact hc t le_rfl]
        rw [if_neg hft]
        unfold r repairSchedule
        simp
      have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q'') := by
        rw [schedCache_fifoSchedule σ C₀ (t + 1)]
        unfold cacheSeq Policy.step
        rw [← schedCache_fifoSchedule σ C₀ t]
        rw [if_neg (by rw [← hagree t le_rfl]; exact hft)]
        congr 2
        · rw [hagree t le_rfl]
        · change farthestInFuture (schedCache (fifoSchedule σ C₀) C₀ σ t) σ t = q''
          rw [← hagree t le_rfl]
          rw [← fifo_evict_eq_farthest e σ C₀ hagree]
      rw [hE, hF]

end Caching

end CLRS
