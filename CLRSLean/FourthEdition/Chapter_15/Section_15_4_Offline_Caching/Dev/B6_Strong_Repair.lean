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

/-- If `nextUse σ i p = none`, then no request after `i` (within `σ`) is `p`. -/
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

/-- If `q = e t` at a B2 position is never requested again, then FIF's choice
`q''` there is also never requested again (`q''` is the farthest page, while
`none` is farthest; `farthestInFuture_max`). -/
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

/-- Cache difference of the dead-page repair: `r = repairSchedule e t q'' t`
(same as `e` everywhere except that at `t` it evicts `q''` rather than `q`)
differs from `e`'s cache at every step only by pages in `{q, q''}`.
The requests must avoid `{q, q''}` (`hdead`), which rules out the mixed
hit/fault case.  No keep-swap, no reducedness needed. -/
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
            · -- x ∈ (E_t − q'') and x ∉ E' ⟹ x = q
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
            · -- x ∈ (E_t − q) and x ∉ Ŝ' ⟹ x = q''
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
                · -- x ∈ Ŝ ∩ E: x = e s or x ∉ E' (contradiction) ⟹ x = e s ⟹ evicted by both? no — x ≠ e s — contradiction
                  exfalso
                  -- x ∈ E_s, x ∉ insert σ[s] (E_s − e s) ⟹ x = e s (contradicts hxne) or x = σ[s] (x ∈ E_s, σ[s] ∉ E_s — contradiction)
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
                · -- x ∈ E ∩ Ŝ ⟹ x = e s or σ[s] — contradicts hx.2
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

/-- B2 and `q` never requested again (`q''` likewise never requested again):
the repair `r` differs from `e`'s cache only by `{q, q''}` (both dead pages),
so the miss counts are equal and agreement extends to `t + 1`.
No slack needed. -/
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
      · -- s > t: σ[s] ∉ {q,q''} ⟹ hits align
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
  · -- agree up to t+1
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

/-- Range-restricted difference (`s ≤ J = t + 1 + j`): the dead-page repair
`r` differs from `e`'s cache only by pages in `{q, q''}`, up to `q`'s next
request (`J`). -/
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
            · -- x ∈ (E_t − q'') and x ∉ E' ⟹ x = q
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
            · -- x ∈ (E_t − q) and x ∉ Ŝ' ⟹ x = q''
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
                · -- x ∈ Ŝ ∩ E: x = e s or σ[s], contradicts hx.2
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
                · -- x ∈ E ∩ Ŝ ⟹ x = e s or σ[s] — contradicts hx.2
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

/-- Dead-page repair after `J = t + 1 + j`: `E_s − Ŝ_s ⊆ {q''}` (`q''` is
dead, never requested), so a request that hits `e`'s cache also hits `r`'s
(`rF ≤ eF` after `J`).  The base case needs the good event `hqkept`: `r`
hits at `J` (`q ∈ Ŝ_J`). -/
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
      · -- base: s+1 = J+1: r hits at J (cache unchanged), e faults and evicts e J
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
        · -- x = q: q ∈ Ŝ (r hits at J, cache unchanged) — contradiction
          exfalso
          exact hx.2 (by
            rw [hS]
            exact hxr ▸ hqkept)
        · -- x ∈ E_J − e J: x ∉ Ŝ_J ⟹ x = q'' (the e − Ŝ direction of hJdiff)
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
          · -- x = q: contradicts hx.2 (q ∈ Ŝ_J)
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
        · -- e hits ⟹ r hits (σ[s] ∈ E_s − Ŝ_s ⊆ {q''} ⟹ σ[s] = q'' contradiction)
          rw [if_pos he]
          have hsigS : σ.getD s 0 ∈ schedCache r C₀ σ s := by
            by_contra hnot
            have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hnot⟩
            exact hneq_sig (Finset.mem_singleton.mp (hih hmem))
          rw [if_pos hsigS]
          -- both caches unchanged, difference preserved
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_singleton]
          have hmem : x ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
            rw [Finset.mem_sdiff]
            exact ⟨hx.1, hx.2⟩
          exact Finset.mem_singleton.mp (hih hmem)
        · -- e faults
          rw [if_neg he]
          by_cases hr : σ.getD s 0 ∈ schedCache r C₀ σ s
          · -- r hits: rF = 0 ≤ eF = 1 (r's cache unchanged)
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
          · -- both fault
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

/-- B2 and `q = e t` will be requested again (next at `J = t + 1 + j`), while
`q''` is never requested again: the repair `r = repairSchedule e t q'' t`
differs from `e` before `J` only by `{q, q''}` (requests avoid `{q, q''}`);
at `J`, `r` hits and `e` faults (`hqkept`, the good event); after `J`,
`E_s − Ŝ_s ⊆ {q''}` (dead page `q''` is never requested), so pointwise
`rF ≤ eF`, the miss count does not increase, and agreement extends to
`t + 1`.  No slack needed. -/
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
        · -- inside (t, J]: at J, r hits and e faults; for t < s < J requests avoid {q,q''}
          by_cases hs_eqJ : s = t + 1 + j
          · -- s = J: r hits (q ∈ Ŝ_J), e faults (swap_q_not_mem)
            subst s
            have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
            have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
              exact swap_q_not_mem e σ C₀ (show e t = q from rfl) hqin hft hj (by omega) le_rfl
            rw [hsig]
            rw [if_pos (by simpa [q, r, q''] using hqkept)]
            rw [if_neg hqnotE]
            omega
          · -- t < s < J: hdead applies, hits/faults align
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
        · -- s > J: E_s − Ŝ_s ⊆ {q''} (hdiff_after), e hits ⟹ r hits
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
            · -- r hits: rF = 0 ≤ eF = 1
              rw [if_pos hr]
              omega
            · -- both fault
              rw [if_neg hr]
    unfold schedMisses
    exact Finset.sum_le_sum (fun s hs => hpoint s (Finset.mem_range.mp hs))
  · -- agree up to t+1
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

/-- Strong version of the B2 repair: when `q = e t` and
`q'' = fifoSchedule σ C₀ t` are both requested again, and the swap form
holds at `J = t + 1 + j` (`hswap`, i.e. keep-swap), the miss count
**does not increase** (the good event at `J` offsets the bad event at `J''`),
and agreement extends to `t + 1`.  No slack needed. -/
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
    · -- misses: rF ≤ eF + 1{J'}, and rF J = 0, eF J = 1, so the sums cancel
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
          · -- inside (t, J]
            by_cases hs_eqJ : s = t + 1 + j
            · -- s = J: requests q, `e` faults, `r` hits (keep-swap)
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
            · -- t < s < J: inside the window, the request is neither q nor q'
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
            · -- inside (J, J')
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
              · -- s = J': rF ≤ eF + 1 holds trivially
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
      -- at J: rF = 0 (keep-swap), eF = 1 (q ∉ E)
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

/-- The alive-alive B2's exact net (DESIGN.md's non-q₀' pairing proposal,
credit 2): the strong repair's pointwise balance is
`rF = eF − 1{J} + 1{bad at J''}` — the good at `J` (the repair hits where
the source faults — keep-swap) can occur without the bad at `J''` (the
source hits `q''` there), in which case the repair saves exactly 1.
Formal: `schedMisses r + 1 ≤ schedMisses e + bad` — the slack credit
`+1 − bad` that covers a later B1's bad on the kept page. -/
lemma repair_step_swap_exact_net (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
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
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ + 1 ≤
      schedMisses e C₀ σ +
        if σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j') then 1 else 0 := by
  let q : Page := e t
  let q' : Page := fifoSchedule σ C₀ t
  let r : ℕ → Page := repairSchedule e t q' (t + 1 + j')
  let eF : ℕ → ℕ := schedFaultAt e C₀ σ
  let rF : ℕ → ℕ := schedFaultAt r C₀ σ
  let bad : ℕ := if σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j') then 1 else 0
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
  have hq : q = e t := rfl
  have hqne : q ≠ q' := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    intro hqq'
    exact hfd.2.1 (by rw [← hq, hqq'])
  have hJlen : t + 1 + j < σ.length := by
    have hjlt' : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt'
    omega
  have hJ'len : t + 1 + j' < σ.length := by
    have hj'lt' : j' < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj').1
    rw [List.length_drop] at hj'lt'
    omega
  -- pointwise over the range without J': rF + 1{J} ≤ eF
  have hper' : ∀ s, s < σ.length → s ≠ t + 1 + j' →
      rF s + (if s = t + 1 + j then 1 else 0) ≤ eF s := by
    intro s hlen hsneq
    by_cases hst : s ≤ t
    · unfold rF eF r schedFaultAt
      rw [schedCache_repairSchedule_eq_e e t q' (t + 1 + j') (by omega) σ C₀ hst]
      rw [show (if s = t + 1 + j then 1 else 0) = 0 by
        simp [show s ≠ t + 1 + j by omega]]
      omega
    · have hts' : t < s := by omega
      by_cases hsJ : s ≤ t + 1 + j
      · -- inside (t, J]
        by_cases hs_eqJ : s = t + 1 + j
        · -- s = J: requests q, `e` faults, `r` hits (keep-swap) — the repair saves 1
          subst s
          unfold rF eF r schedFaultAt
          have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
          have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
            exact swap_q_not_mem e σ C₀ hq hqin hft hj (by omega) le_rfl
          rw [hsig]
          rw [show (if t + 1 + j = t + 1 + j then 1 else 0) = 1 by simp]
          have hqinS : q ∈ schedCache r C₀ σ (t + 1 + j) := by
            rw [hswap]
            rw [hq]
            exact Finset.mem_insert_self _ _
          rw [if_pos hqinS]
          rw [if_neg hqnotE]
        · -- t < s < J: inside the window, the request is neither q nor q'
          have hwin := repairSchedule_window_swap' e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj'
            (s := s) (by omega) (by omega)
          unfold rF eF r schedFaultAt
          rw [show (if s = t + 1 + j then 1 else 0) = 0 by
            simp [show s ≠ t + 1 + j by omega]]
          rcases hwin with hswap' | hsub
          · rw [hswap']
            have hneq_q : σ.getD s 0 ≠ q := getD_ne_nextUse (k := s) hj (by omega) (by omega)
            have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
            by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hr]
              rw [if_pos (by
                rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q', hr⟩))]
            · rw [if_neg hr]
              have hr' : σ.getD s 0 ∉ insert q ((schedCache e C₀ σ s).erase q') := by
                intro hm
                rcases Finset.mem_insert.mp hm with hqq | hm
                · exact hneq_q hqq
                · exact hr (Finset.mem_erase.mp hm).2
              rw [if_neg hr']
          · rw [hsub]
            have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
            by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hr]
              rw [if_pos (Finset.mem_erase.mpr ⟨hneq_q', hr⟩)]
            · rw [if_neg hr]
              have hr' : σ.getD s 0 ∉ (schedCache e C₀ σ s).erase q' := by
                intro hm
                exact hr (Finset.mem_erase.mp hm).2
              rw [if_neg hr']
      · -- s > J
        by_cases hsJ' : s < t + 1 + j'
        · -- inside (J, J')
          have hwin := repairSchedule_after_J_window e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj'
            (s := s) (by omega) (by omega)
          unfold rF eF r schedFaultAt
          rw [show (if s = t + 1 + j then 1 else 0) = 0 by
            simp [show s ≠ t + 1 + j by omega]]
          rcases hwin with hsub | ⟨x, hswap''⟩
          · rw [hsub]
            have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
            by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hr]
              rw [if_pos (Finset.mem_erase.mpr ⟨hneq_q', hr⟩)]
            · rw [if_neg hr]
              have hr' : σ.getD s 0 ∉ (schedCache e C₀ σ s).erase q' := by
                intro hm
                exact hr (Finset.mem_erase.mp hm).2
              rw [if_neg hr']
          · rw [hswap'']
            have hneq_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
            by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hr]
              rw [if_pos (by
                rw [Finset.mem_insert]
                exact Or.inr (Finset.mem_erase.mpr ⟨hneq_q', hr⟩))]
            · rw [if_neg hr]
              by_cases hrS : σ.getD s 0 ∈ insert x ((schedCache e C₀ σ s).erase q')
              · rw [if_pos hrS]
                omega
              · rw [if_neg hrS]
        · -- s > J':E ⊆ Ŝ
          have hsJ'' : t + 1 + j' < s := by omega
          have hsup : schedCache e C₀ σ s ⊆ schedCache r C₀ σ s := by
            exact repairSchedule_superset_swap e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj' hsJ''
          unfold rF eF r schedFaultAt
          rw [show (if s = t + 1 + j then 1 else 0) = 0 by
            simp [show s ≠ t + 1 + j by omega]]
          by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
          · rw [if_pos hr]
            rw [if_pos (hsup hr)]
          · rw [if_neg hr]
            by_cases hr' : σ.getD s 0 ∈ schedCache r C₀ σ s
            · rw [if_pos hr']
              omega
            · rw [if_neg hr']
  -- sum: Σ rF + 1 ≤ Σ eF + bad (+1 at J; at J', eF + bad = 1 and rF ≤ 1)
  unfold schedMisses
  change (∑ s ∈ Finset.range σ.length, rF s) + 1 ≤
    (∑ s ∈ Finset.range σ.length, eF s) + bad
  have hJin : t + 1 + j ∈ Finset.range σ.length := by
    rw [Finset.mem_range]
    exact hJlen
  have hJ'in : t + 1 + j' ∈ Finset.range σ.length := by
    rw [Finset.mem_range]
    exact hJ'len
  have hJneJ' : t + 1 + j ≠ t + 1 + j' := by omega
  have hsum_erase_le : (Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) rF) + 1 ≤
      Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) eF := by
    have hper_sum : Finset.sum ((Finset.range σ.length).erase (t + 1 + j'))
          (fun s => rF s + (if s = t + 1 + j then 1 else 0)) ≤
        Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) eF := by
      exact Finset.sum_le_sum (fun s hs => hper' s
        (Finset.mem_range.mp (Finset.mem_erase.mp hs).2) (Finset.mem_erase.mp hs).1)
    rw [Finset.sum_add_distrib] at hper_sum
    have hsum_good : Finset.sum ((Finset.range σ.length).erase (t + 1 + j'))
        (fun s => (if s = t + 1 + j then 1 else 0)) = 1 := by
      rw [Finset.sum_eq_single (t + 1 + j)]
      · simp
      · intro b hb hbne
        simp [hbne]
      · intro hnot
        exfalso
        exact hnot (Finset.mem_erase.mpr ⟨hJneJ', hJin⟩)
    rw [hsum_good] at hper_sum
    omega
  have heFJ'add : eF (t + 1 + j') + bad = 1 := by
    by_cases hbad : σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j')
    · unfold bad eF schedFaultAt
      rw [if_pos hbad, if_pos hbad]
    · unfold bad eF schedFaultAt
      rw [if_neg hbad, if_neg hbad]
  have hrFJ'le : rF (t + 1 + j') ≤ 1 := by
    unfold rF schedFaultAt
    split <;> omega
  have hsum_erase_r : (Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) rF) +
      rF (t + 1 + j') = Finset.sum (Finset.range σ.length) rF := by
    exact Finset.sum_erase_add (s := Finset.range σ.length) (a := t + 1 + j')
      (f := rF) hJ'in
  have hsum_erase_e : (Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) eF) +
      eF (t + 1 + j') = Finset.sum (Finset.range σ.length) eF := by
    exact Finset.sum_erase_add (s := Finset.range σ.length) (a := t + 1 + j')
      (f := eF) hJ'in
  rw [← hsum_erase_r, ← hsum_erase_e]
  have hA : (Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) rF + rF (t + 1 + j')) + 1 ≤
      Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) eF + 1 := by
    omega
  have hB : Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) eF + 1 ≤
      Finset.sum ((Finset.range σ.length).erase (t + 1 + j')) eF + eF (t + 1 + j') + bad := by
    omega
  exact le_trans hA hB

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

/-- keep-swap derivation: at a B2 position `t₂` inside the exchange window
`(t₀, J₀']`, the repair's swap form `Ŝ = insert q (E − q'')` is preserved
on `(t₂, J]` (in particular up to `J`).  Inductive step:
`exchange_no_evict_q` rules out the flip `e s = q`; the remaining cases
preserve the form. -/
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
          · -- r hits ⟹ e hits, both caches unchanged, form preserved
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
            -- three cases for e s
            by_cases hes_q : e s = q
            · exfalso
              exact exchange_no_evict_q d t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
                ht₂₀ ht₂₁ (show e t₂ = q from rfl) hqin hft₂ hj (s := s) (by omega) (by omega)
                hsigE' hes_q
            · by_cases hes_q'' : e s = q''
              · -- e s = q'': both erases are no-ops
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
              · -- e s ∉ {q, q''}: the erases commute, form preserved
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

/-- When `q`'s next request is at `J = t + 1 + j` and `q''` is never
requested again, the requests inside `(t, J)` avoid `{q, q''}`
(`getD_ne_nextUse` + `getD_ne_of_nextUse_none`, with the length bound given
by `hj`).  Shared construction for the dead-page repair difference lemmas. -/
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

/-- The dead-page repair (nop is `t`) agrees with `e` before `t`
(`schedCache_repairSchedule_eq_e` requires `t < nop`, which does not apply
when nop = `t`). -/
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

/-- A dead page `q` (`nextUse = none`), once evicted by `e` at `t`, never
returns to `e`'s cache (the dead-page version of `swap_q_not_mem`; `e`
inserts `σ[s]` only on faults, and `σ[s] ≠ q`). -/
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

/-- B1 (no-op) alive-alive window difference: when `q''`'s next request is at
`J''' = t + 1 + j'''`, the repair `r = repairSchedule e t q'' (t + 1 + j''')`
differs from `e`'s cache on `(t, J''']` only by `{q''}` (`E − Ŝ ⊆ {q''}` and
`Ŝ ⊆ E`).  Isomorphic to `repair_diff_noop_qp_dead`, except that the requests
avoiding `q''` is given by `hj'''` and the range is restricted to
`s ≤ t + 1 + j'''`. -/
lemma repair_diff_noop_window (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hnoop : e t ∉ schedCache e C₀ σ t)
    (hft : σ.getD t 0 ∉ schedCache e C₀ σ t)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t)
    {j''' : ℕ} (hj''' : nextUse σ (t + 1) q'' = some j''') :
    ∀ s, s ≤ t + 1 + j''' →
      schedCache e C₀ σ s \ schedCache (repairSchedule e t q'' (t + 1 + j''')) C₀ σ s ⊆
          ({q''} : Finset Page) ∧
      schedCache (repairSchedule e t q'' (t + 1 + j''')) C₀ σ s ⊆ schedCache e C₀ σ s := by
  let r : ℕ → Page := repairSchedule e t q'' (t + 1 + j''')
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
            rw [schedCache_repairSchedule_eq_e e t q'' (t + 1 + j''') (by omega) σ C₀ hs_le_t]
            exact hx.1)
        · intro x hx
          rw [← schedCache_repairSchedule_eq_e e t q'' (t + 1 + j''') (by omega) σ C₀ hs_le_t]
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
            rw [schedCache_repairSchedule_eq_e e t q'' (t + 1 + j''') (by omega) σ C₀ le_rfl]
            rw [if_neg hft]
            unfold r repairSchedule
            simp
          constructor
          · -- E' − Ŝ' ⊆ {q''}
            intro x hx
            rw [Finset.mem_sdiff] at hx
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp (hE ▸ hx.1) with hxr | hxE
            · -- x = σ[t]: contradicts x ∈ Ŝ'
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
          have hsJ : s < t + 1 + j''' := by omega
          have hsig_ne : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj''' (by omega) (by omega)
          -- hits/faults align (E − Ŝ ⊆ {q''} and Ŝ ⊆ E)
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
          rw [show repairSchedule e t q'' (t + 1 + j''') s = e s by
            unfold repairSchedule
            simp [show s ≠ t by omega, show s ≠ t + 1 + j''' by omega]]
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
                · -- x ∈ E ∩ Ŝ ⟹ x = e s or σ[s] — contradicts hx.2
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

/-- B1 (no-op) and `q'' = fifoSchedule σ C₀ t` is never requested again: the
repair `r = repairSchedule e t q'' t` differs from `e`'s cache only by
`{q''}` (`E − Ŝ ⊆ {q''}`), and `Ŝ ⊆ E`.  `e`'s eviction at `t` is a no-op
(`hnoop`, `E_{t+1} = insert σ[t] E_t`), while `r` evicts `q''` at `t`;
afterwards the requests avoid `q''` (`hq''dead`), both follow `e` (`s ≠ t`),
and the difference set no longer grows. -/
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
            · -- x = σ[t]: contradicts x ∈ Ŝ'
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
          -- hits/faults align (E − Ŝ ⊆ {q''} and Ŝ ⊆ E)
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
                · -- x ∈ E ∩ Ŝ ⟹ x = e s or σ[s] — contradicts hx.2
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

/-- B1 (no-op) and `q'' = fifoSchedule σ C₀ t` is never requested again: the
repair `r = repairSchedule e t q'' t` differs from `e`'s cache only by
`{q''}` (`e`'s eviction at `t` is a no-op, `r` evicts `q''`; afterwards the
requests avoid `q''`), so the miss counts are equal and agreement extends to
`t + 1`.  The bad event is impossible (`q''` is dead), so no slack needed. -/
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
        · -- e hits ⟹ r hits (σ[s] ∈ E − Ŝ ⊆ {q''} contradiction)
          rw [if_pos he]
          rw [if_pos (by
            by_contra hr
            have hmem : σ.getD s 0 ∈ schedCache e C₀ σ s \ schedCache r C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨he, hr⟩
            exact hneq_q'' (Finset.mem_singleton.mp ((hdiff s (by omega)).1 hmem)))]
        · -- e faults ⟹ r faults (Ŝ ⊆ E)
          rw [if_neg he]
          rw [if_neg (by
            intro hr
            exact he ((hdiff s (by omega)).2 hr))]
    unfold schedMisses
    rw [Finset.sum_congr rfl (by
      intro s hs
      exact hpoint s (Finset.mem_range.mp hs))]
  · -- agree up to t+1
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

/-- Base-case swap form of the dead-page repair (nop is `t`):
`Ŝ_{t+1} = insert q (E_{t+1} − q')`.  The nop = `t + 1 + j'` version of
`repairSchedule_base_swap` requires `t < nop` (via
`schedCache_repairSchedule_eq_e`); here we give the nop = `t` version
(equal caches up to `t` via the local `hce`). -/
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

/-- keep-swap derivation (q'' dead version): at a B2 position `t₂` where
`q''` is never requested again, the dead-page repair
`r = repairSchedule e t₂ q'' t₂` has its swap form `Ŝ = insert q (E − q'')`
preserved on `(t₂, J]` (in particular up to `J` — the good event
`q ∈ Ŝ_J`).  Isomorphic to `repair_keep_swap`: the requests avoiding `q''`
come from `hq''dead` instead of `hj''` (`getD_ne_of_nextUse_none`, needs
`hJlen`), and the repair's nop is `t₂` instead of `t₂ + 1 + j''`. -/
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
          · -- r hits ⟹ e hits, both caches unchanged, form preserved
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
            -- three cases for e s
            by_cases hes_q : e s = q
            · exfalso
              exact exchange_no_evict_q d t₀ q₀ q₀' σ C₀ hweak hft₀ hq₀'res hj₀'
                ht₂₀ ht₂₁ (show e t₂ = q from rfl) hqin hft₂ hj (s := s) (by omega) (by omega)
                hsigE' hes_q
            · by_cases hes_q'' : e s = q''
              · -- e s = q'': both erases are no-ops
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
              · -- e s ∉ {q, q''}: the erases commute, form preserved
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
