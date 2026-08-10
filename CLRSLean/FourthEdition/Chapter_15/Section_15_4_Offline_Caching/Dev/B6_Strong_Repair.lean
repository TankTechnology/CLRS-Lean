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
- `repair_step_swap_qp_dead`: `q''` dead (`q` alive) ⟹ `schedMisses r ≤
  schedMisses e` and agreement extends (free)
- `repair_step_qp_dead`: B1 no-op with `q''` dead ⟹ `schedMisses r ≤
  schedMisses e` and agreement extends (free, bad event impossible)
- `repair_step_swap_strong`: keep-swap form at `J` ⟹ `schedMisses r ≤
  schedMisses e` and agreement extends (no slack)
- `exchange_no_evict_q`: in the exchange window, the exchange never evicts
  `q` on `(t₂, J]` (branch 1 evicts `q₀'`, branches 4-6 evict pages of `C'`,
  branch 5 evicts `d s` — none can be `q`)
- `repair_keep_swap`: the swap form survives to `J` in the exchange window
- `repair_keep_swap_qp_dead`: same, `q''` dead — the swap form (hence the
  good event `q ∈ Ŝ_J`) for the dead-page repair `repairSchedule e t₂ q'' t₂`

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
    exact hget' ▸ List.getElem_mem hslt
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

/-- 范围受限的差集(`s ≤ J = t + 1 + j`):死页修复 `r` 与 `e` 的 cache
只差 `{q, q''}` 中的页,直到 `q` 的下一次请求(`J`)之前。 -/
lemma repair_cache_diff_le (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : e t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hdead : ∀ s, t < s → s < t + 1 + j → σ.getD s 0 ∉ ({q, q''} : Finset Page)) :
    ∀ s, s ≤ t + 1 + j →
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
        · -- step:t < s
          have hst : t < s := by omega
          have hs_ne : s ≠ t := by omega
          have hsJ : s < t + 1 + j := by omega
          have hmem_eq : (σ.getD s 0 ∈ schedCache r C₀ σ s) ↔
              (σ.getD s 0 ∈ schedCache e C₀ σ s) := by
            constructor
            · intro hr
              by_contra he
              have hmem : σ.getD s 0 ∈ schedCache r C₀ σ s \ schedCache e C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hr, he⟩
              exact hdead s hst hsJ ((ih (by omega)).1 hmem)
            · intro he
              by_contra hr
              have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨he, hr⟩
              exact hdead s hst hsJ ((ih (by omega)).2 hmem)
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
                · -- x ∈ Ŝ ∩ E:x = e s 或 σ[s],与 hx.2 矛盾
                  exfalso
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

/-- 死页修复在 `J = t + 1 + j` 之后:`E_s − Ŝ_s ⊆ {q''}`(`q''` 死、永不
请求),故请求命中 `e` 的 cache 时也命中 `r` 的(`rF ≤ eF` 在 `J` 之后)。
基例需要好事件 `hqkept`:`r` 于 `J` 处命中(`q ∈ Ŝ_J`)。 -/
lemma repair_cache_diff_after (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q q'' : Page} (hq : e t = q) (hq'' : q'' = fifoSchedule σ C₀ t)
    (hqin : q ∈ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqq'' : q ≠ q'')
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq''dead : nextUse σ (t + 1) q'' = none)
    (hqkept : q ∈ schedCache (repairSchedule e t q'' t) C₀ σ (t + 1 + j))
    (hdiff : ∀ s, s ≤ t + 1 + j →
      (schedCache (repairSchedule e t q'' t) C₀ σ s \ schedCache e C₀ σ s) ⊆
          ({q, q''} : Finset Page) ∧
      (schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' t) C₀ σ s) ⊆
          ({q, q''} : Finset Page)) :
    ∀ s, t + 1 + j < s → s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' t) C₀ σ s ⊆
          ({q''} : Finset Page) := by
  let r : ℕ → Page := repairSchedule e t q'' t
  have hr_ne : ∀ s, s ≠ t → r s = e s := by
    intro s hs
    simp [r, repairSchedule, hs]
  have hq''ne : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q'' := by
    intro s hs1 hs2
    exact getD_ne_of_nextUse_none σ hq''dead hs1 hs2
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hsJ hslen
      have hslt : s < σ.length := by omega
      by_cases hs_eq : s = t + 1 + j
      · -- base:s+1 = J+1:r 命中于 J(cache 不变),e 缺页并逐出 e J
        subst s
        have hJdiff := hdiff (t + 1 + j) le_rfl
        have hS : schedCache r C₀ σ (t + 1 + j + 1) = schedCache r C₀ σ (t + 1 + j) := by
          rw [schedCache]
          have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
          rw [hsig]
          rw [if_pos hqkept]
        have hE : schedCache e C₀ σ (t + 1 + j + 1) =
            insert q ((schedCache e C₀ σ (t + 1 + j)).erase (e (t + 1 + j))) := by
          rw [schedCache]
          have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
          have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
            exact swap_q_not_mem e σ C₀ hq hqin hft hj (by omega) le_rfl
          rw [hsig]
          rw [if_neg hqnotE]
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_singleton]
        have hxJdiff := hJdiff
        rcases Finset.mem_insert.mp (hE ▸ hx.1) with hxr | hxE
        · -- x = q:q ∈ Ŝ(r 命中于 J,cache 不变)——矛盾
          exfalso
          exact hx.2 (by
            rw [hS]
            exact hxr ▸ hqkept)
        · -- x ∈ E_J − e J:x ∉ Ŝ_J ⟹ x = q''(hJdiff 的 e − Ŝ 方向)
          have hxin : x ∈ schedCache e C₀ σ (t + 1 + j) := (Finset.mem_erase.mp hxE).2
          have hxne : x ≠ e (t + 1 + j) := (Finset.mem_erase.mp hxE).1
          have hxnotS : x ∉ schedCache r C₀ σ (t + 1 + j) := by
            intro hxS
            exact hx.2 (by rw [hS]; exact hxS)
          have hmem : x ∈ schedCache e C₀ σ (t + 1 + j) \
              schedCache r C₀ σ (t + 1 + j) := by
            rw [Finset.mem_sdiff]
            exact ⟨hxin, hxnotS⟩
          have hq' := (hJdiff.2 hmem)
          rcases Finset.mem_insert.mp hq' with hqeq | hq'eq
          · -- x = q:与 hx.2 矛盾(q ∈ Ŝ_J)
            exfalso
            exact hx.2 (by rw [hS]; exact hqeq ▸ hqkept)
          · exact Finset.mem_singleton.mp hq'eq
      · -- step:s > J
        have hsJ' : t + 1 + j < s := by omega
        have hih := ih hsJ' (by omega)
        have hneq_sig : σ.getD s 0 ≠ q'' := hq''ne s (by omega) hslt
        -- r s = e s(s ≠ t)
        rw [schedCache, schedCache]
        rw [show repairSchedule e t q'' t s = e s by
          unfold repairSchedule
          simp [show s ≠ t by omega]]
        by_cases he : σ.getD s 0 ∈ schedCache e C₀ σ s
        · -- e 命中 ⟹ r 命中(σ[s] ∈ E_s − Ŝ_s ⊆ {q''} ⟹ σ[s] = q'' 矛盾)
          rw [if_pos he]
          have hsigS : σ.getD s 0 ∈ schedCache r C₀ σ s := by
            by_contra hnot
            have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hnot⟩
            exact hneq_sig (Finset.mem_singleton.mp (hih hmem))
          rw [if_pos hsigS]
          -- 双方 cache 不变,差集保持
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_singleton]
          have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
            rw [Finset.mem_sdiff]
            exact ⟨hx.1, hx.2⟩
          exact Finset.mem_singleton.mp (hih hmem)
        · -- e 缺页
          rw [if_neg he]
          by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
          · -- r 命中:rF = 0 ≤ eF = 1(r 的 cache 不变)
            rw [if_pos hr]
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE
            · exfalso
              exact hx.2 (hxr ▸ hr)
            · -- x ∈ E_s − e s,x ∉ Ŝ_s ⟹ x = q''
              have hxin : x ∈ schedCache e C₀ σ s := (Finset.mem_erase.mp hxE).2
              have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, hx.2⟩
              exact Finset.mem_singleton.mp (hih hmem)
          · -- 双方缺页
            rw [if_neg hr]
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE
            · exfalso
              exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
            · -- x ∈ E_s − e s,x ∉ insert σ[s] (Ŝ_s − e s) ⟹ x = q''
              have hxin : x ∈ schedCache e C₀ σ s := (Finset.mem_erase.mp hxE).2
              have hxne : x ≠ e s := (Finset.mem_erase.mp hxE).1
              have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, by
                  intro hxS
                  by_cases hxeq : x = σ.getD s 0
                  · exact he (hxeq.symm ▸ hxin)
                  · exact hx.2 (Finset.mem_insert.mpr
                      (Or.inr (Finset.mem_erase.mpr ⟨hxne, hxS⟩)))⟩
              exact Finset.mem_singleton.mp (hih hmem)

/-- B2 且 `q = e t` 仍会再次请求(下次在 `J = t + 1 + j`)、`q''` 永不再
请求:修复 `r = repairSchedule e t q'' t` 与 `e` 在 `J` 前只差 `{q, q''}`
(请求避开 `{q, q''}`),`J` 处 `r` 命中而 `e` 缺页(`hqkept`,好事件),
`J` 后 `E_s − Ŝ_s ⊆ {q''}`(死页 `q''` 永不请求),故逐点 `rF ≤ eF`,
miss 数不增,一致性扩展到 `t + 1`。无需 slack。 -/
lemma repair_step_swap_qp_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) (e t) = some j)
    (hq''dead : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none)
    (hqkept : e t ∈ schedCache (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ
      (t + 1 + j)) :
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ ≤ schedMisses e C₀ σ ∧
    agreeWithFIF (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ (t + 1) := by
  let q : Page := e t
  let q'' : Page := fifoSchedule σ C₀ t
  let r : ℕ → Page := repairSchedule e t q'' t
  have hqq'' : q ≠ q'' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq
    exact hfd.2.1 (by simpa [q, q'', hqq])
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    exact hfd.1
  have hJlen : t + 1 + j < σ.length := by
    have hjlt : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt
    omega
  have hdead : ∀ s, t < s → s < t + 1 + j → σ.getD s 0 ∉ ({q, q''} : Finset Page) := by
    intro s hst hsJ hmem
    rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
    · exact getD_ne_nextUse (k := s) hj (by omega) (by omega) hqeq
    · exact getD_ne_of_nextUse_none σ (by simpa [q''] using hq''dead) (by omega) (by omega)
        (Finset.mem_singleton.mp hq'eq)
  have hdiff := repair_cache_diff_le e σ C₀ (show e t = q from rfl) rfl hft hqq'' hj hdead
  have hq''ne : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q'' := by
    intro s hs1 hs2
    exact getD_ne_of_nextUse_none σ (by simpa [q''] using hq''dead) hs1 hs2
  have hdiff_after := repair_cache_diff_after e σ C₀ (show e t = q from rfl) rfl hqin hft
    hqq'' hj (by simpa [q''] using hq''dead) (by simpa [q] using hqkept) hdiff
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
  · -- misses:rF ≤ eF pointwise
    have hpoint : ∀ s, s < σ.length → schedFaultAt r C₀ σ s ≤ schedFaultAt e C₀ σ s := by
      intro s hs
      unfold schedFaultAt
      by_cases hs_le_t : s ≤ t
      · -- s ≤ t:caches equal
        rw [hc s hs_le_t]
      · by_cases hsJ : s ≤ t + 1 + j
        · -- (t, J] 内:J 处 r 命中、e 缺页;t < s < J 请求避开 {q,q''}
          by_cases hs_eqJ : s = t + 1 + j
          · -- s = J:r 命中(q ∈ Ŝ_J),e 缺页(swap_q_not_mem)
            subst s
            have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
            have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
              exact swap_q_not_mem e σ C₀ (show e t = q from rfl) hqin hft hj (by omega) le_rfl
            rw [hsig]
            rw [if_pos (by simpa [q, r, q''] using hqkept)]
            rw [if_neg hqnotE]
            omega
          · -- t < s < J:hdead 适用,hit/fault 对齐
            have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
            have hneq_q'' : σ.getD s 0 ≠ q'' := hq''ne s (by omega) (by omega)
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
        · -- s > J:E_s − Ŝ_s ⊆ {q''}(hdiff_after),e 命中 ⟹ r 命中
          have hsJ'' : t + 1 + j < s := by omega
          have hsig_ne : σ.getD s 0 ≠ q'' := hq''ne s (by omega) (by omega)
          by_cases he : σ.getD s 0 ∈ schedCache e C₀ σ s
          · rw [if_pos he]
            rw [if_pos (by
              by_contra hr
              have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨he, hr⟩
              exact hsig_ne (Finset.mem_singleton.mp ((hdiff_after s hsJ'' (by omega)) hmem)))]
          · rw [if_neg he]
            by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
            · -- r 命中:rF = 0 ≤ eF = 1
              rw [if_pos hr]
              omega
            · -- 双方缺页
              rw [if_neg hr]
    unfold schedMisses
    exact Finset.sum_le_sum (fun s hs => hpoint s (Finset.mem_range.mp hs))
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

/-- B2 修复的强版本:`q = e t` 与 `q'' = fifoSchedule σ C₀ t` 都会再次被
请求,且 swap 形式在 `J = t + 1 + j` 处保持(`hswap`,即 keep-swap)时,
miss 数**不增**(好事件在 `J` 抵消坏事件在 `J''`),一致性扩展到 `t + 1`。
无需 slack。 -/
lemma repair_step_swap_strong (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) (e t) = some j)
    {j' : ℕ} (hj' : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = some j')
    (hjj' : j < j')
    (hswap : schedCache (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ (t + 1 + j) =
      insert (e t) ((schedCache e C₀ σ (t + 1 + j)).erase (fifoSchedule σ C₀ t))) :
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ ≤
      schedMisses e C₀ σ ∧
    agreeWithFIF (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ (t + 1) := by
  let q : Page := e t
  let q' : Page := fifoSchedule σ C₀ t
  let r : ℕ → Page := repairSchedule e t q' (t + 1 + j')
  let eF : ℕ → ℕ := schedFaultAt e C₀ σ
  let rF : ℕ → ℕ := schedFaultAt r C₀ σ
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
    exact hfd.2.2
  have hsig_ne : σ.getD t 0 ≠ q' := by
    intro hsig
    exact hft (hsig ▸ hq'res)
  have hJ'len : t + 1 + j' < σ.length := by
    have hj'lt' : j' < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj').1
    rw [List.length_drop] at hj'lt'
    omega
  have hJlen : t + 1 + j < σ.length := by
    have hjlt' : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt'
    omega
  have hq : q = e t := rfl
  have hqne : q ≠ q' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq'
    exact hfd.2.1 (by rw [← hq, hqq'])
  have hfifo : nextUse σ (t + 1) q' = none ∨
      ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' := by
    apply fifo_nextUse_order σ (schedCache e C₀ σ t) t q' q
    · exact fifo_evict_eq_farthest e σ C₀ hagree
    · exact hqin
    · exact hqne
  rcases hfifo with hnone | ⟨j0, j0', hj0, hj0', hjlt⟩
  · exfalso
    rw [hj'] at hnone
    contradiction
  · have hj0eq : j0 = j := Option.some.inj (hj0.symm.trans hj)
    have hj0'eq : j0' = j' := Option.some.inj (hj0'.symm.trans hj')
    have hjj'0 : j0 < j0' := by omega
    have hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j0 → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact getD_ne_nextUse (k := k) hj' (by omega) (by omega)
    constructor
    · -- misses:rF ≤ eF + 1{J'},且 rF J = 0、eF J = 1,和式相消
      have hper : ∀ s, s < σ.length → rF s ≤ eF s + (if s = t + 1 + j' then 1 else 0) := by
        intro s hlen
        by_cases hst : s ≤ t
        · unfold rF eF r schedFaultAt
          rw [schedCache_repairSchedule_eq_e e t q' (t + 1 + j') (by omega) σ C₀ hst]
          rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
            simp [show s ≠ t + 1 + j' by omega]]
          omega
        · have hts' : t < s := by omega
          by_cases hsJ : s ≤ t + 1 + j
          · -- (t, J] 内
            by_cases hs_eqJ : s = t + 1 + j
            · -- s = J:请求 q,`e` 缺页,`r` 命中(keep-swap)
              subst s
              unfold rF eF r schedFaultAt
              have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
              have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
                exact swap_q_not_mem e σ C₀ hq hqin hft hj (by omega) le_rfl
              rw [hsig]
              rw [show (if t + 1 + j = t + 1 + j' then 1 else 0) = 0 by
                simp [show j ≠ j' by omega]]
              have hqinS : q ∈ schedCache r C₀ σ (t + 1 + j) := by
                rw [hswap]
                rw [hq]
                exact Finset.mem_insert_self _ _
              rw [if_pos hqinS]
              rw [if_neg hqnotE]
              omega
            · -- t < s < J:窗口内,请求既不是 q 也不是 q'
              have hwin := repairSchedule_window_swap' e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj'
                (s := s) (by omega) (by omega)
              unfold rF eF r schedFaultAt
              rcases hwin with hswap' | hsub
              · -- Ŝ = insert q (E − q')
                rw [hswap']
                have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
                have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
                by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
                · rw [if_pos hr]
                  rw [if_pos (by
                    rw [Finset.mem_insert]
                    exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q', hr⟩))]
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
                · rw [if_neg hr]
                  have hr' : σ.getD s 0 ∉ insert q ((schedCache e C₀ σ s).erase q') := by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqq | hm
                    · exact hneq_q hqq
                    · exact hr (Finset.mem_erase.mp hm).2
                  rw [if_neg hr']
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
              · -- Ŝ = E − q'
                rw [hsub]
                have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
                by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
                · rw [if_pos hr]
                  rw [if_pos (Finset.mem_erase.mpr ⟨hneq_q', hr⟩)]
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
                · rw [if_neg hr]
                  have hr' : σ.getD s 0 ∉ (schedCache e C₀ σ s).erase q' := by
                    intro hm
                    exact hr (Finset.mem_erase.mp hm).2
                  rw [if_neg hr']
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
          · -- s > J
            by_cases hsJ' : s < t + 1 + j'
            · -- (J, J') 内
              have hwin := repairSchedule_after_J_window e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj'
                (s := s) (by omega) (by omega)
              unfold rF eF r schedFaultAt
              rcases hwin with hsub | ⟨x, hswap''⟩
              · -- Ŝ = E − q'
                rw [hsub]
                have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
                by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
                · rw [if_pos hr]
                  rw [if_pos (Finset.mem_erase.mpr ⟨hneq_q', hr⟩)]
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
                · rw [if_neg hr]
                  have hr' : σ.getD s 0 ∉ (schedCache e C₀ σ s).erase q' := by
                    intro hm
                    exact hr (Finset.mem_erase.mp hm).2
                  rw [if_neg hr']
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
              · -- Ŝ = insert x (E − q')
                rw [hswap'']
                have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
                by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
                · rw [if_pos hr]
                  rw [if_pos (by
                    rw [Finset.mem_insert]
                    exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q', hr⟩))]
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
                · rw [if_neg hr]
                  by_cases hrS : σ.getD s 0 ∈ insert x ((schedCache e C₀ σ s).erase q')
                  · rw [if_pos hrS]
                    rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                      simp [show s ≠ t + 1 + j' by omega]]
                    omega
                  · rw [if_neg hrS]
                    rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                      simp [show s ≠ t + 1 + j' by omega]]
            · -- s ≥ J'
              by_cases hs_eqJ' : s = t + 1 + j'
              · -- s = J':rF ≤ eF + 1 恒真
                subst s
                unfold rF eF r schedFaultAt
                rw [show (if t + 1 + j' = t + 1 + j' then 1 else 0) = 1 by simp]
                by_cases hr : σ.getD (t + 1 + j') 0 ∈ schedCache r C₀ σ (t + 1 + j')
                · rw [if_pos hr]
                  omega
                · rw [if_neg hr]
                  omega
              · -- s > J':E ⊆ Ŝ
                have hsJ'' : t + 1 + j' < s := by omega
                have hsup : schedCache e C₀ σ s ⊆ schedCache r C₀ σ s := by
                  exact repairSchedule_superset_swap e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj' hsJ''
                unfold rF eF r schedFaultAt
                by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
                · rw [if_pos hr]
                  rw [if_pos (hsup hr)]
                  rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                    simp [show s ≠ t + 1 + j' by omega]]
                · rw [if_neg hr]
                  by_cases hr' : σ.getD s 0 ∈ schedCache r C₀ σ s
                  · rw [if_pos hr']
                    rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                      simp [show s ≠ t + 1 + j' by omega]]
                    omega
                  · rw [if_neg hr']
                    rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                      simp [show s ≠ t + 1 + j' by omega]]
      unfold schedMisses
      change (∑ s ∈ Finset.range σ.length, rF s) ≤ (∑ s ∈ Finset.range σ.length, eF s)
      -- J 处:rF = 0(keep-swap),eF = 1(q ∉ E)
      have hrFJ : rF (t + 1 + j) = 0 := by
        unfold rF schedFaultAt
        rw [hswap]
        rw [show σ.getD (t + 1 + j) 0 = q by exact getD_eq_nextUse hj]
        rw [hq]
        rw [if_pos (Finset.mem_insert_self _ _)]
      have heFJ : eF (t + 1 + j) = 1 := by
        unfold eF schedFaultAt
        rw [show σ.getD (t + 1 + j) 0 = q by exact getD_eq_nextUse hj]
        have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
          exact swap_q_not_mem e σ C₀ hq hqin hft hj (by omega) le_rfl
        rw [if_neg hqnotE]
      have hJin : t + 1 + j ∈ Finset.range σ.length := by
        rw [Finset.mem_range]
        exact hJlen
      have hJ'in : t + 1 + j' ∈ Finset.range σ.length := by
        rw [Finset.mem_range]
        exact hJ'len
      have hJneJ' : t + 1 + j ≠ t + 1 + j' := by omega
      have hsum_erase : (∑ s ∈ (Finset.range σ.length).erase (t + 1 + j), rF s) + rF (t + 1 + j) =
          ∑ s ∈ Finset.range σ.length, rF s := by
        exact Finset.sum_erase_add (s := Finset.range σ.length) (a := t + 1 + j) (f := rF) hJin
      have hle_erase : (∑ s ∈ (Finset.range σ.length).erase (t + 1 + j), rF s) ≤
          ∑ s ∈ (Finset.range σ.length).erase (t + 1 + j),
            (eF s + (if s = t + 1 + j' then 1 else 0)) := by
        exact Finset.sum_le_sum (fun s hs => hper s (by
          exact Finset.mem_range.mp (Finset.mem_erase.mp hs).2))
      have hsum2 : (∑ s ∈ (Finset.range σ.length).erase (t + 1 + j),
            (eF s + (if s = t + 1 + j' then 1 else 0))) =
          (∑ s ∈ (Finset.range σ.length).erase (t + 1 + j), eF s) + 1 := by
        rw [Finset.sum_add_distrib]
        rw [show (∑ s ∈ (Finset.range σ.length).erase (t + 1 + j),
            (if s = t + 1 + j' then 1 else 0)) = 1 by
          rw [Finset.sum_ite_eq']
          have hmem' : t + 1 + j' ∈ (Finset.range σ.length).erase (t + 1 + j) := by
            rw [Finset.mem_erase]
            exact ⟨Ne.symm hJneJ', hJ'in⟩
          rw [if_pos hmem']]
      have hsum3 : (∑ s ∈ (Finset.range σ.length).erase (t + 1 + j), eF s) =
          (∑ s ∈ Finset.range σ.length, eF s) - 1 := by
        have h := Finset.sum_erase_add (s := Finset.range σ.length) (a := t + 1 + j) (f := eF) hJin
        rw [heFJ] at h
        omega
      have hsum_ge : 1 ≤ ∑ s ∈ Finset.range σ.length, eF s := by
        rw [← heFJ]
        exact Finset.single_le_sum (fun s hs => Nat.zero_le _) hJin
      omega
    · -- agree through t + 1
      intro s hs
      by_cases hs' : s ≤ t
      · rw [schedCache_repairSchedule_eq_e e t q' (t + 1 + j') (by omega) σ C₀ hs']
        exact hagree s hs'
      · have hst : s = t + 1 := by omega
        subst s
        have hbase : schedCache r C₀ σ (t + 1) = insert q ((schedCache e C₀ σ (t + 1)).erase q') := by
          exact repairSchedule_base_swap e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj'
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
        have hE : schedCache r C₀ σ (t + 1) =
            insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
          rw [hbase]
          rw [schedCache]
          rw [if_neg hft]
          rw [← hq]
          rw [Finset.erase_insert_of_ne hsig_ne]
          rw [Finset.insert_comm]
          congr 1
          have herase : ((schedCache e C₀ σ t).erase q).erase q' =
              ((schedCache e C₀ σ t).erase q').erase q := by
            ext x
            simp [Finset.mem_erase, and_left_comm, and_assoc]
          rw [herase]
          exact Finset.insert_erase (Finset.mem_erase.mpr ⟨hqne, hqin⟩)
        rw [hE, hF]

/-- In the exchange window of `t₀`, at a B2 position `t₂`, the exchange
schedule never evicts `q = e t₂` at a fault in `(t₂, J]`: branch 1 evicts
the window page `q₀'` (absent from the cache while `q` is resident),
branches 4-6 evict pages of `C'` minus `E` (and `q ∉ E_s`), branch 5
evicts `d s` (which would force `q ∈ C'`).  The core of keep-swap. -/
lemma exchange_no_evict_q (d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d C₀ σ t₀)
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    {q : Page} (hq : (exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂ = q)
    (hqin : q ∈ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hft₂ : σ.getD t₂ 0 ∉ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) q = some j)
    {s : ℕ} (hs1 : t₂ < s) (hs2 : s ≤ t₂ + 1 + j)
    (hFault : σ.getD s 0 ∉ schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ s) :
    (exchangeSchedule d t₀ q₀ q₀' σ C₀) s ≠ q := by
  let e : ℕ → Page := exchangeSchedule d t₀ q₀ q₀' σ C₀
  have hq₀'neq : q₀' ≠ q := by
    intro hqeq
    have hq₀'not : q₀' ∉ schedCache e C₀ σ t₂ := by
      exact exchangeSchedule_q'_absent d t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀' ht₂₀ (by omega)
    exact hq₀'not (hqeq ▸ hqin)
  have hqnotE : q ∉ schedCache e C₀ σ s := by
    exact swap_q_not_mem e σ C₀ hq hqin hft₂ hj (by omega) hs2
  change (exchangeScheduleCore d t₀ q₀ q₀' σ C₀ s).2 ≠ q
  rw [exchangeScheduleCore_second]
  rw [← schedCache_exchangeScheduleCore]
  change exchangeDecision d t₀ q₀ q₀' σ C₀ (schedCache e C₀ σ s) s ≠ q
  unfold exchangeDecision
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  by_cases h1 : d s = q₀'
  · rw [if_pos h1]
    exact hq₀'neq
  · rw [if_neg h1]
    by_cases hb4 : (σ.getD s 0 = q₀' ∨ σ.getD s 0 = q₀) ∧
        σ.getD s 0 ∈ schedCache d C₀ σ s
    · rw [if_pos hb4]
      let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
      by_cases hf : (M.filter (fun x => x ≠ q₀')).Nonempty
      · rw [dif_pos hf]
        intro hqeq
        have hmem : Classical.choose hf ∈ schedCache e C₀ σ s :=
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Classical.choose_spec hf)).1).1
        exact hqnotE (hqeq ▸ hmem)
      · by_cases hm : M.Nonempty
        · rw [dif_neg hf]
          rw [dif_pos hm]
          intro hqeq
          have hmem : Classical.choose hm ∈ schedCache e C₀ σ s :=
            (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
          exact hqnotE (hqeq ▸ hmem)
        · rw [dif_neg hf]
          rw [dif_neg hm]
          exfalso
          have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
            rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t₀ q₀ q₀' σ C₀ s).1 by
              rw [← schedCache_exchangeScheduleCore]]
            exact exchangeScheduleCore_card d t₀ q₀ q₀' σ C₀ hweak (by omega)
          have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          exact hFault (hEq.symm ▸ hb4.2)
    · rw [if_neg hb4]
      by_cases hdsin : d s ∈ schedCache e C₀ σ s
      · rw [if_pos hdsin]
        intro hqeq
        exact hqnotE (hqeq ▸ hdsin)
      · rw [if_neg hdsin]
        let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
        by_cases hm : M.Nonempty
        · rw [dif_pos hm]
          intro hqeq
          have hmem : Classical.choose hm ∈ schedCache e C₀ σ s :=
            (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
          exact hqnotE (hqeq ▸ hmem)
        · rw [dif_neg hm]
          exfalso
          have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
            rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t₀ q₀ q₀' σ C₀ s).1 by
              rw [← schedCache_exchangeScheduleCore]]
            exact exchangeScheduleCore_card d t₀ q₀ q₀' σ C₀ hweak (by omega)
          have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          have hdFault : σ.getD s 0 ∉ schedCache d C₀ σ s := by
            intro h
            exact hFault (hEq.symm ▸ h)
          have hdsE : d s ∈ schedCache d C₀ σ s := hweak s (by omega) hdFault
          exact hdsin (hEq.symm ▸ hdsE)

/-- keep-swap 推导:交换窗口 `(t₀, J₀']` 内的 B2 位置 `t₂` 处,repair 的
swap 形式 `Ŝ = insert q (E − q'')` 在 `(t₂, J]` 上保持(尤其到 `J`)。
归纳步:`exchange_no_evict_q` 排除 `e s = q` 的翻转,其余情形形式保持。 -/
lemma repair_keep_swap (d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hagree : agreeWithFIF (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hdis : schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t₂ + 1) ≠
      schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : (exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂ ∈
      schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) ((exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂) = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j'')
    (hjj'' : j < j'') :
    schedCache (repairSchedule (exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂
        (fifoSchedule σ C₀ t₂) (t₂ + 1 + j'')) C₀ σ (t₂ + 1 + j) =
      insert ((exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂)
        ((schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t₂ + 1 + j)).erase
          (fifoSchedule σ C₀ t₂)) := by
  let e : ℕ → Page := exchangeSchedule d t₀ q₀ q₀' σ C₀
  let q : Page := e t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule e t₂ q'' (t₂ + 1 + j'')
  have hft₂ : σ.getD t₂ 0 ∉ schedCache e C₀ σ t₂ := by
    exact (first_disagree e σ C₀ hC₀ ht₂ hagree hdis).1
  have hqne'' : q ≠ q'' := by
    intro hqq
    exact (first_disagree e σ C₀ hC₀ ht₂ hagree hdis).2.1 (by simpa [q, q'', hqq])
  have hsig_ne : σ.getD t₂ 0 ≠ q'' := by
    intro hsig
    exact hft₂ (hsig ▸ (by
      have hq''in : q'' ∈ schedCache e C₀ σ t₂ := by
        simpa [q''] using (first_disagree e σ C₀ hC₀ ht₂ hagree hdis).2.2
      exact hq''in))
  have hmain : ∀ s, t₂ + 1 ≤ s → s ≤ t₂ + 1 + j →
      schedCache r C₀ σ s = insert q ((schedCache e C₀ σ s).erase q'') := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hs_eq : s = t₂
        · -- base:s+1 = t₂+1
          subst s
          exact repairSchedule_base_swap e σ C₀ hC₀ ht₂ hagree hdis hqin rfl (show q = e t₂ from rfl) hj''
        · -- step:t₂ < s
          have hst : t₂ < s := by omega
          have hs1' : t₂ + 1 ≤ s := by omega
          have hs2' : s ≤ t₂ + 1 + j := by omega
          have hih := ih hs1' hs2'
          have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
          have hneq_q'' : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj'' (by omega) (by omega)
          have hds : r s = e s := by
            unfold r repairSchedule
            simp [show s ≠ t₂ by omega, show s ≠ t₂ + 1 + j'' by omega]
          rw [schedCache, schedCache]
          rw [hds]
          by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
          · -- r hits ⟹ e hits,双方 cache 不变,形式保持
            rw [if_pos hr]
            have hsigE : σ.getD s 0 ∈ schedCache e C₀ σ s := by
              rw [hih] at hr
              rcases Finset.mem_insert.mp hr with hqeq | hm
              · exfalso
                exact hneq_q hqeq
              · exact (Finset.mem_erase.mp hm).2
            rw [if_pos hsigE]
            rw [hih]
          · -- both fault
            have hsigE' : σ.getD s 0 ∉ schedCache e C₀ σ s := by
              intro h
              have hm : σ.getD s 0 ∈ insert q ((schedCache e C₀ σ s).erase q'') := by
                rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q'', h⟩)
              exact hr (hih ▸ hm)
            rw [if_neg hr]
            rw [if_neg hsigE']
            rw [hih]
            -- e s 的三种情形
            by_cases hes_q : e s = q
            · exfalso
              exact exchange_no_evict_q d t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
                ht₂₀ ht₂₁ (show e t₂ = q from rfl) hqin hft₂ hj (s := s) (by omega) (by omega)
                hsigE' hes_q
            · by_cases hes_q'' : e s = q''
              · -- e s = q'':双方的 erase 都是 no-op
                rw [hes_q'']
                rw [show (insert q ((schedCache e C₀ σ s).erase q'')).erase q'' =
                    insert q ((schedCache e C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hqne'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [show (insert (σ.getD s 0) ((schedCache e C₀ σ s).erase q'')).erase q'' =
                    insert (σ.getD s 0) ((schedCache e C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hneq_q'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [Finset.insert_comm]
              · -- e s ∉ {q, q''}:erase 交换,形式保持
                have hne_q : e s ≠ q := hes_q
                have hne_q'' : e s ≠ q'' := hes_q''
                rw [Finset.erase_insert_of_ne (a := q) (b := e s) (Ne.symm hne_q)]
                rw [Finset.erase_insert_of_ne (a := σ.getD s 0) (b := q'') hneq_q'']
                have herase_comm : ((schedCache e C₀ σ s).erase (e s)).erase q'' =
                    ((schedCache e C₀ σ s).erase q'').erase (e s) := by
                  ext x
                  simp [Finset.mem_erase, and_left_comm, and_assoc]
                rw [herase_comm]
                rw [Finset.insert_comm]
  exact hmain (t₂ + 1 + j) (by omega) le_rfl

/-- `q` 的下次请求在 `J = t + 1 + j`、`q''` 永不再请求时,`(t, J)` 内的
请求避开 `{q, q''}`(`getD_ne_nextUse` + `getD_ne_of_nextUse_none`,长度界
由 `hj` 给出)。死页修复差集引理的共用构造。 -/
lemma repair_requests_avoid_q_qp (σ : List Page) {t : ℕ} {q q'' : Page} {j : ℕ}
    (hj : nextUse σ (t + 1) q = some j) (hq''dead : nextUse σ (t + 1) q'' = none) :
    ∀ s, t < s → s < t + 1 + j → σ.getD s 0 ∉ ({q, q''} : Finset Page) := by
  have hJlen : t + 1 + j < σ.length := by
    have hjlt : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt
    omega
  intro s hst hsJ hmem
  rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
  · exact getD_ne_nextUse (k := s) hj (by omega) (by omega) hqeq
  · exact getD_ne_of_nextUse_none σ hq''dead (by omega) (by omega)
      (Finset.mem_singleton.mp hq'eq)

/-- 死页修复(nop 即 `t`)的 cache 在 `t` 前与 `e` 一致
(`schedCache_repairSchedule_eq_e` 需要 `t < nop`,nop = `t` 时不适用)。 -/
lemma schedCache_repairSchedule_eq_e_qp_dead (e : ℕ → Page) (t : ℕ) (q' : Page)
    (σ : List Page) (C₀ : Finset Page) {s : ℕ} (hs : s ≤ t) :
    schedCache (repairSchedule e t q' t) C₀ σ s = schedCache e C₀ σ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [schedCache, schedCache]
      rw [ih (by omega)]
      unfold repairSchedule
      simp [show s ≠ t by omega]

/-- 死页 `q`(`nextUse = none`)在 `t` 处被 `e` 逐出后永不回到 `e` 的 cache
(`swap_q_not_mem` 的死页版;e 只在缺页时插入 `σ[s]`,而 `σ[s] ≠ q`)。 -/
lemma swap_q_not_mem_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} {q : Page} (hq : e t = q) (hqin : q ∈ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    (hqdead : nextUse σ (t + 1) q = none)
    {s : ℕ} (hs1 : t < s) (hs2 : s < σ.length) :
    q ∉ schedCache e C₀ σ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t
      · subst s
        rw [schedCache]
        rw [if_neg hft]
        intro hm
        rw [Finset.mem_insert] at hm
        rcases hm with hqr | hqin2
        · have h : σ.getD t 0 ∈ schedCache e C₀ σ t := by
            rwa [← hqr]
          exact hft h
        · exact (Finset.mem_erase.mp hqin2).1 hq.symm
      · have hts : t < s := by omega
        have hsig_ne : σ.getD s 0 ≠ q := getD_ne_of_nextUse_none σ hqdead (by omega) (by omega)
        rw [schedCache]
        by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hr]
          exact ih hts (by omega)
        · rw [if_neg hr]
          intro hm
          rcases Finset.mem_insert.mp hm with hqr | hqin2
          · exact hsig_ne hqr.symm
          · exact ih hts (by omega) (Finset.mem_erase.mp hqin2).2

/-- B1(no-op)且 `q'' = fifoSchedule σ C₀ t` 永不再请求:修复
`r = repairSchedule e t q'' t` 的 cache 与 `e` 的只差 `{q''}`
(`E − Ŝ ⊆ {q''}`),且 `Ŝ ⊆ E`。`e` 于 `t` 的逐出是 no-op(`hnoop`,
`E_{t+1} = insert σ[t] E_t`),`r` 于 `t` 逐出 `q''`;此后请求避开 `q''`
(`hq''dead`),双方都跟随 `e`(`s ≠ t`),差集不再增长。 -/
lemma repair_diff_noop_qp_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hnoop : e t ∉ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t)
    (hq''dead : nextUse σ (t + 1) q'' = none) :
    ∀ s, s ≤ σ.length →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' t) C₀ σ s ⊆
          ({q''} : Finset Page) ∧
      schedCache (repairSchedule e t q'' t) C₀ σ s ⊆ schedCache e C₀ σ s := by
  let r : ℕ → Page := repairSchedule e t q'' t
  intro s
  induction s with
  | zero =>
      intro hlen
      constructor
      · intro x hx
        exfalso
        simp [schedCache] at hx
      · intro x hx
        exact hx
  | succ s ih =>
      intro hlen
      by_cases hs_le_t : s + 1 ≤ t
      · -- s+1 ≤ t:caches equal
        constructor
        · intro x hx
          rw [Finset.mem_sdiff] at hx
          exfalso
          exact hx.2 (by
            rw [schedCache_repairSchedule_eq_e_qp_dead e t q'' σ C₀ hs_le_t]
            exact hx.1)
        · intro x hx
          rw [← schedCache_repairSchedule_eq_e_qp_dead e t q'' σ C₀ hs_le_t]
          exact hx
      · by_cases hs_eq : s = t
        · -- base:s+1 = t+1
          subst s
          have hE : schedCache e C₀ σ (t + 1) = insert (σ.getD t 0) (schedCache e C₀ σ t) := by
            rw [schedCache]
            rw [if_neg hft]
            rw [Finset.erase_eq_of_notMem hnoop]
          have hS : schedCache r C₀ σ (t + 1) =
              insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q'') := by
            rw [schedCache]
            rw [schedCache_repairSchedule_eq_e_qp_dead e t q'' σ C₀ le_rfl]
            rw [if_neg hft]
            unfold r repairSchedule
            simp
          constructor
          · -- E' − Ŝ' ⊆ {q''}
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp (hE ▸ hx.1) with hxr | hxE
            · -- x = σ[t]:x ∈ Ŝ' 矛盾
              exfalso
              exact hx.2 (hS ▸ (Finset.mem_insert.mpr (Or.inl hxr)))
            · -- x ∈ E_t,x ∉ insert σ[t] (E_t − q'') ⟹ x = q''
              by_cases hxq : x = q''
              · exact hxq
              · exfalso
                exact hx.2 (hS ▸ (Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_erase.mpr ⟨hxq, hxE⟩))))
          · -- Ŝ' ⊆ E'
            intro x hx
            rw [hS] at hx
            rw [Finset.mem_insert] at hx
            rcases hx with hxr | hxS
            · rw [hE]
              exact Finset.mem_insert.mpr (Or.inl hxr)
            · rw [hE]
              exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mp hxS).2)
        · -- step:t < s
          have hst : t < s := by omega
          have hsig_ne : σ.getD s 0 ≠ q'' := by
            exact getD_ne_of_nextUse_none σ (by simpa [hq''] using hq''dead) (by omega) (by omega)
          -- hit/fault 对齐(E − Ŝ ⊆ {q''} 且 Ŝ ⊆ E)
          have hmem_eq : (σ.getD s 0 ∈ schedCache r C₀ σ s) ↔
              (σ.getD s 0 ∈ schedCache e C₀ σ s) := by
            constructor
            · intro hr
              by_contra he
              exact he ((ih (by omega)).2 hr)
            · intro he
              by_contra hr
              have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨he, hr⟩
              exact hsig_ne (Finset.mem_singleton.mp ((ih (by omega)).1 hmem))
          rw [schedCache, schedCache]
          rw [show repairSchedule e t q'' t s = e s by
            unfold repairSchedule
            simp [show s ≠ t by omega]]
          by_cases hfault : σ.getD s 0 ∈ schedCache e C₀ σ s
          · -- both hit:caches unchanged
            rw [if_pos hfault, if_pos (hmem_eq.mpr hfault)]
            exact ih (by omega)
          · -- both fault
            rw [if_neg hfault, if_neg (by intro hr; exact hfault (hmem_eq.mp hr))]
            constructor
            · -- E' − Ŝ' ⊆ {q''}
              intro x hx
              rw [Finset.mem_sdiff] at hx
              rw [Finset.mem_singleton]
              rcases Finset.mem_insert.mp hx.1 with hxr | hxE
              · exfalso
                exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
              · -- x ∈ E_s − e s,x ∉ insert σ[s] (Ŝ_s − e s)
                have hxin : x ∈ schedCache e C₀ σ s := (Finset.mem_erase.mp hxE).2
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
                · -- x ∈ E − Ŝ ⊆ {q''}
                  have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
                    rw [Finset.mem_sdiff]
                    exact ⟨hxin, hxS⟩
                  exact Finset.mem_singleton.mp ((ih (by omega)).1 hmem)
            · -- Ŝ' ⊆ E'
              intro x hx
              rw [Finset.mem_insert] at hx
              rcases hx with hxr | hxS
              · rw [Finset.mem_insert]
                exact Or.inl hxr
              · rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr
                  ⟨(Finset.mem_erase.mp hxS).1, (ih (by omega)).2 (Finset.mem_erase.mp hxS).2⟩)

/-- B1(no-op)且 `q'' = fifoSchedule σ C₀ t` 永不再请求:修复
`r = repairSchedule e t q'' t` 与 `e` 的 cache 只差 `{q''}`(`e` 于 `t` 的
逐出是 no-op,`r` 逐出 `q''`;此后请求避开 `q''`),故 miss 数相同,一致性
扩展到 `t + 1`。坏事件不可能(`q''` 死),无需 slack。 -/
lemma repair_step_qp_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    (hq''dead : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none) :
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ ≤ schedMisses e C₀ σ ∧
    agreeWithFIF (repairSchedule e t (fifoSchedule σ C₀ t) t) C₀ σ (t + 1) := by
  let q'' : Page := fifoSchedule σ C₀ t
  let r : ℕ → Page := repairSchedule e t q'' t
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
  have hce : ∀ s, s ≤ t → schedCache r C₀ σ s = schedCache e C₀ σ s := by
    intro s hs
    exact schedCache_repairSchedule_eq_e_qp_dead e t q'' σ C₀ hs
  have hdiff := repair_diff_noop_qp_dead e σ C₀ hnoop hft rfl hq''dead
  constructor
  · -- misses:rF = eF pointwise
    have hpoint : ∀ s, s < σ.length → schedFaultAt r C₀ σ s = schedFaultAt e C₀ σ s := by
      intro s hs
      unfold schedFaultAt
      by_cases hs_le_t : s ≤ t
      · -- caches equal
        rw [hce s hs_le_t]
      · have hst : t < s := by omega
        have hneq_q'' : σ.getD s 0 ≠ q'' := by
          exact getD_ne_of_nextUse_none σ (by simpa [q''] using hq''dead) (by omega) (by omega)
        by_cases he : σ.getD s 0 ∈ schedCache e C₀ σ s
        · -- e 命中 ⟹ r 命中(σ[s] ∈ E − Ŝ ⊆ {q''} 矛盾)
          rw [if_pos he]
          rw [if_pos (by
            by_contra hr
            have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hr⟩
            exact hneq_q'' (Finset.mem_singleton.mp ((hdiff s (by omega)).1 hmem)))]
        · -- e 缺页 ⟹ r 缺页(Ŝ ⊆ E)
          rw [if_neg he]
          rw [if_neg (by
            intro hr
            exact he ((hdiff s (by omega)).2 hr))]
    unfold schedMisses
    rw [Finset.sum_congr rfl (by
      intro s hs
      exact hpoint s (Finset.mem_range.mp hs))]
  · -- agree 到 t+1
    intro s hs
    by_cases hs' : s ≤ t
    · -- s ≤ t:caches equal
      rw [hce s hs']
      exact hagree s hs'
    · have hst : s = t + 1 := by omega
      subst s
      have hq''res : q'' ∈ schedCache e C₀ σ t := by
        have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
        simpa [q''] using hfd.2.2
      have hsig_ne : σ.getD t 0 ≠ q'' := by
        intro hsig
        exact hft (hsig ▸ hq''res)
      have hE : schedCache r C₀ σ (t + 1) = insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q'') := by
        rw [schedCache]
        rw [show schedCache r C₀ σ t = schedCache e C₀ σ t by
          exact hce t le_rfl]
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

/-- 死页修复(nop 即 `t`)的基例 swap 形式:`Ŝ_{t+1} = insert q (E_{t+1} − q')`。
`repairSchedule_base_swap` 的 nop = `t + 1 + j'` 版本需要 `t < nop`(经
`schedCache_repairSchedule_eq_e`),这里给出 nop = `t` 的版本(等 cache 到
`t` 用局部 `hce`)。 -/
lemma repairSchedule_base_swap_qp_dead (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    (hq : q = e t) :
    schedCache (repairSchedule e t q' t) C₀ σ (t + 1) =
      insert q ((schedCache e C₀ σ (t + 1)).erase q') := by
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
  have hqne : q ≠ q' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq'
    exact hfd.2.1 (by rw [← hq, ← hq']; exact hqq')
  have hsig_ne_q' : σ.getD t 0 ≠ q' := by
    intro hsig
    exact hft (hsig ▸ hq'res)
  have hsig_ne_q : σ.getD t 0 ≠ q := by
    intro hsig
    exact hft (hsig ▸ hq ▸ hqin)
  have hce : ∀ s, s ≤ t → schedCache (repairSchedule e t q' t) C₀ σ s =
      schedCache e C₀ σ s := by
    intro s hs
    induction s with
    | zero => rfl
    | succ s ih =>
        have hst : s ≤ t := by omega
        have hst' : s ≠ t := by omega
        rw [schedCache, schedCache]
        rw [ih hst]
        unfold repairSchedule
        simp [hst']
  rw [schedCache]
  rw [hce t le_rfl]
  rw [repairSchedule_at_t]
  rw [if_neg hft]
  rw [schedCache]
  rw [if_neg hft]
  rw [← hq]
  rw [Finset.erase_insert_of_ne hsig_ne_q']
  have hqin' : q ∈ schedCache e C₀ σ t := by
    rw [hq]
    exact hqin
  have hE : (schedCache e C₀ σ t).erase q' =
      insert q (((schedCache e C₀ σ t).erase q).erase q') := by
    ext x
    constructor
    · intro hx
      have hxq' : x ≠ q' := (Finset.mem_erase.mp hx).1
      have hxin : x ∈ schedCache e C₀ σ t := (Finset.mem_erase.mp hx).2
      rw [Finset.mem_insert]
      by_cases hxq : x = q
      · exact Or.inl hxq
      · exact Or.inr (Finset.mem_erase.mpr ⟨hxq', Finset.mem_erase.mpr ⟨hxq, hxin⟩⟩)
    · intro hx
      rw [Finset.mem_insert] at hx
      rcases hx with hxq | hxin
      · rw [hxq]
        exact Finset.mem_erase.mpr ⟨hqne, hqin'⟩
      · have hx' := Finset.mem_erase.mp (Finset.mem_erase.mp hxin).2
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxin).1, hx'.2⟩
  rw [hE]
  rw [Finset.insert_comm]

/-- keep-swap 推导(q'' 死版):`q''` 永不再请求的 B2 位置 `t₂` 处,死页修复
`r = repairSchedule e t₂ q'' t₂` 的 swap 形式 `Ŝ = insert q (E − q'')` 在
`(t₂, J]` 上保持(尤其到 `J` —— 好事件 `q ∈ Ŝ_J`)。与 `repair_keep_swap`
同构:请求避开 `q''` 由 `hj''` 换为 `hq''dead`(`getD_ne_of_nextUse_none`,
需要 `hJlen`),repair 的 nop 由 `t₂ + 1 + j''` 换为 `t₂`。 -/
lemma repair_keep_swap_qp_dead (d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hq₀ : d t₀ = q₀) (hqq₀ : q₀ ≠ q₀')
    (hweak : ∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft₀ : σ.getD t₀ 0 ∉ schedCache d C₀ σ t₀)
    (hq₀'res : q₀' ∈ schedCache d C₀ σ t₀)
    {j₀ : ℕ} (hj₀ : nextUse σ (t₀ + 1) q₀ = some j₀)
    (hq₀'ne : ∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀')
    {j₀' : ℕ} (hj₀' : nextUse σ (t₀ + 1) q₀' = some j₀')
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hagree : agreeWithFIF (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hdis : schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t₂ + 1) ≠
      schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : (exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂ ∈
      schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) ((exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂) = some j)
    (hq''dead : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = none) :
    schedCache (repairSchedule (exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂
        (fifoSchedule σ C₀ t₂) t₂) C₀ σ (t₂ + 1 + j) =
      insert ((exchangeSchedule d t₀ q₀ q₀' σ C₀) t₂)
        ((schedCache (exchangeSchedule d t₀ q₀ q₀' σ C₀) C₀ σ (t₂ + 1 + j)).erase
          (fifoSchedule σ C₀ t₂)) := by
  let e : ℕ → Page := exchangeSchedule d t₀ q₀ q₀' σ C₀
  let q : Page := e t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule e t₂ q'' t₂
  have hft₂ : σ.getD t₂ 0 ∉ schedCache e C₀ σ t₂ := by
    exact (first_disagree e σ C₀ hC₀ ht₂ hagree hdis).1
  have hqne'' : q ≠ q'' := by
    intro hqq
    exact (first_disagree e σ C₀ hC₀ ht₂ hagree hdis).2.1 (by simpa [q, q'', hqq])
  have hsig_ne : σ.getD t₂ 0 ≠ q'' := by
    intro hsig
    exact hft₂ (hsig ▸ (by
      have hq''in : q'' ∈ schedCache e C₀ σ t₂ := by
        simpa [q''] using (first_disagree e σ C₀ hC₀ ht₂ hagree hdis).2.2
      exact hq''in))
  have hJlen : t₂ + 1 + j < σ.length := by
    have hjlt : j < (σ.drop (t₂ + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt
    omega
  have hmain : ∀ s, t₂ + 1 ≤ s → s ≤ t₂ + 1 + j →
      schedCache r C₀ σ s = insert q ((schedCache e C₀ σ s).erase q'') := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hs_eq : s = t₂
        · -- base:s+1 = t₂+1
          subst s
          exact repairSchedule_base_swap_qp_dead e σ C₀ hC₀ ht₂ hagree hdis hqin rfl
            (show q = e t₂ from rfl)
        · -- step:t₂ < s
          have hst : t₂ < s := by omega
          have hs1' : t₂ + 1 ≤ s := by omega
          have hs2' : s ≤ t₂ + 1 + j := by omega
          have hih := ih hs1' hs2'
          have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
          have hneq_q'' : σ.getD s 0 ≠ q'' := getD_ne_of_nextUse_none σ
            (by simpa [q''] using hq''dead) (by omega) (by omega)
          have hds : r s = e s := by
            unfold r repairSchedule
            simp [show s ≠ t₂ by omega]
          rw [schedCache, schedCache]
          rw [hds]
          by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
          · -- r hits ⟹ e hits,双方 cache 不变,形式保持
            rw [if_pos hr]
            have hsigE : σ.getD s 0 ∈ schedCache e C₀ σ s := by
              rw [hih] at hr
              rcases Finset.mem_insert.mp hr with hqeq | hm
              · exfalso
                exact hneq_q hqeq
              · exact (Finset.mem_erase.mp hm).2
            rw [if_pos hsigE]
            rw [hih]
          · -- both fault
            have hsigE' : σ.getD s 0 ∉ schedCache e C₀ σ s := by
              intro h
              have hm : σ.getD s 0 ∈ insert q ((schedCache e C₀ σ s).erase q'') := by
                rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q'', h⟩)
              exact hr (hih ▸ hm)
            rw [if_neg hr]
            rw [if_neg hsigE']
            rw [hih]
            -- e s 的三种情形
            by_cases hes_q : e s = q
            · exfalso
              exact exchange_no_evict_q d t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
                ht₂₀ ht₂₁ (show e t₂ = q from rfl) hqin hft₂ hj (s := s) (by omega) (by omega)
                hsigE' hes_q
            · by_cases hes_q'' : e s = q''
              · -- e s = q'':双方的 erase 都是 no-op
                rw [hes_q'']
                rw [show (insert q ((schedCache e C₀ σ s).erase q'')).erase q'' =
                    insert q ((schedCache e C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hqne'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [show (insert (σ.getD s 0) ((schedCache e C₀ σ s).erase q'')).erase q'' =
                    insert (σ.getD s 0) ((schedCache e C₀ σ s).erase q'') by
                  exact Finset.erase_eq_of_notMem (by
                    intro hm
                    rcases Finset.mem_insert.mp hm with hqeq | hmem
                    · exact hneq_q'' hqeq.symm
                    · exact (Finset.mem_erase.mp hmem).1 rfl)]
                rw [Finset.insert_comm]
              · -- e s ∉ {q, q''}:erase 交换,形式保持
                have hne_q : e s ≠ q := hes_q
                have hne_q'' : e s ≠ q'' := hes_q''
                rw [Finset.erase_insert_of_ne (a := q) (b := e s) (Ne.symm hne_q)]
                rw [Finset.erase_insert_of_ne (a := σ.getD s 0) (b := q'') hneq_q'']
                have herase_comm : ((schedCache e C₀ σ s).erase (e s)).erase q'' =
                    ((schedCache e C₀ σ s).erase q'').erase (e s) := by
                  ext x
                  simp [Finset.mem_erase, and_left_comm, and_assoc]
                rw [herase_comm]
                rw [Finset.insert_comm]
  exact hmain (t₂ + 1 + j) (by omega) le_rfl

end Caching

end CLRS
