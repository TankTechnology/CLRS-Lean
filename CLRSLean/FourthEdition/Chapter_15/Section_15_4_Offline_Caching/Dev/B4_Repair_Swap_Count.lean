import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B3_AfterJ_Window

/-!
# Dev B4: the resident (B2) repair counting lemma

Development file for the resident-case repair step of the `fifo_optimal`
iteration (see `Dev/Legacy/StateMachine/DESIGN.md`): when `q = e t` is resident, replacing the
eviction at the first disagreement by the policy's choice (`q'`, evicted
again at its first request) costs at most one extra miss and extends
agreement by one position — the B2 analogue of `repair_step`.

Main results:

- `repairSchedule_superset_swap`: after the first `q'` request, `e`'s cache
  is contained in the repair's
- `repair_step_swap`: `schedMisses (repairSchedule …) ≤ schedMisses e + 1`
  and agreement extends through `t + 1`

This file is part of the `fifo_optimal` iteration; it will be merged into
`S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

/-- B2 analogue of superset: when `q = e t` is resident, after the first
request for `q'`, `e`'s cache is contained in the repair's cache. -/
lemma repairSchedule_superset_swap (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    (hq : q = e t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    (hjj' : j < j')
    {s : ℕ} (hs : t + 1 + j' < s) :
    schedCache e C₀ σ s ⊆ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t + 1 + j'
      · subst s
        -- base: window relation at `J'` + repair evicts `q'` (no-op) then loads it again
        have hwin : schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j') =
              (schedCache e C₀ σ (t + 1 + j')).erase q'
            ∨ ∃ x : Page, schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j') =
              insert x ((schedCache e C₀ σ (t + 1 + j')).erase q') := by
          exact repairSchedule_after_J_window e σ C₀ hC₀ ht hagree hdis hqin hq' hq hj hj' hjj'
            (by omega) (by rfl)
        have hsig : σ.getD (t + 1 + j') 0 = q' := getD_eq_nextUse hj'
        have hrep : repairSchedule e t q' (t + 1 + j') (t + 1 + j') = q' := by
          unfold repairSchedule
          simp
        change (if σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j') then
            schedCache e C₀ σ (t + 1 + j')
          else insert (σ.getD (t + 1 + j') 0)
            ((schedCache e C₀ σ (t + 1 + j')).erase (e (t + 1 + j')))) ⊆
          (if σ.getD (t + 1 + j') 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j')
            then schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j')
          else insert (σ.getD (t + 1 + j') 0)
            ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j')).erase
              (repairSchedule e t q' (t + 1 + j') (t + 1 + j'))))
        rcases hwin with hsub | ⟨x, hswap⟩
        · rw [hsub, hrep]
          rw [hsig]
          simp
          intro x hx
          by_cases hr : q' ∈ schedCache e C₀ σ (t + 1 + j')
          · rw [if_pos hr] at hx
            rw [Finset.mem_insert]
            by_cases hxq' : x = q'
            · exact Or.inl hxq'
            · exact Or.inr (Finset.mem_erase.mpr ⟨hxq', hx⟩)
          · rw [if_neg hr] at hx
            rcases Finset.mem_insert.mp hx with hxq' | hxin
            · rw [hxq']
              rw [Finset.mem_insert]
              exact Or.inl rfl
            · rw [Finset.mem_insert]
              right
              rw [Finset.mem_erase]
              constructor
              · intro hxq'
                exact hr (hxq' ▸ (Finset.mem_erase.mp hxin).2)
              · exact (Finset.mem_erase.mp hxin).2
        · rw [hswap, hrep]
          rw [hsig]
          simp
          intro y hy
          by_cases hr : q' ∈ schedCache e C₀ σ (t + 1 + j')
          · -- `e` hits: `y ∈ E_J'`
            rw [if_pos hr] at hy
            by_cases hqx : q' = x
            · -- the swap page is `q'`
              rw [if_pos hqx]
              rw [← hqx]
              rw [Finset.mem_insert]
              by_cases hyq' : y = q'
              · exact Or.inl hyq'
              · exact Or.inr (Finset.mem_erase.mpr ⟨hyq', hy⟩)
            · -- the swap page is not `q'`
              rw [if_neg hqx]
              have hq'not : q' ∉ insert x ((schedCache e C₀ σ (t + 1 + j')).erase q') := by
                intro hq'in
                rcases Finset.mem_insert.mp hq'in with hq'x | hq'in
                · exact hqx hq'x
                · exact (Finset.mem_erase.mp hq'in).1 rfl
              rw [Finset.erase_eq_of_notMem hq'not]
              rw [Finset.mem_insert]
              by_cases hyq' : y = q'
              · exact Or.inl hyq'
              · exact Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hyq', hy⟩)))
          · -- `e` faults
            rw [if_neg hr] at hy
            rcases Finset.mem_insert.mp hy with hyq' | hyin
            · -- `y = q'`
              rw [hyq']
              by_cases hqx : q' = x
              · rw [if_pos hqx]
                rw [← hqx]
                rw [Finset.mem_insert]
                exact Or.inl rfl
              · rw [if_neg hqx]
                have hq'not : q' ∉ insert x ((schedCache e C₀ σ (t + 1 + j')).erase q') := by
                  intro hq'in
                  rcases Finset.mem_insert.mp hq'in with hq'x | hq'in
                  · exact hqx hq'x
                  · exact (Finset.mem_erase.mp hq'in).1 rfl
                rw [Finset.erase_eq_of_notMem hq'not]
                rw [Finset.mem_insert]
                exact Or.inl rfl
            · -- `y ∈ E_J' − e J'`
              by_cases hqx : q' = x
              · rw [if_pos hqx]
                rw [← hqx]
                rw [Finset.mem_insert]
                by_cases hyq' : y = q'
                · exact Or.inl hyq'
                · exact Or.inr (Finset.mem_erase.mpr ⟨hyq', (Finset.mem_erase.mp hyin).2⟩)
              · rw [if_neg hqx]
                have hq'not : q' ∉ insert x ((schedCache e C₀ σ (t + 1 + j')).erase q') := by
                  intro hq'in
                  rcases Finset.mem_insert.mp hq'in with hq'x | hq'in
                  · exact hqx hq'x
                  · exact (Finset.mem_erase.mp hq'in).1 rfl
                rw [Finset.erase_eq_of_notMem hq'not]
                rw [Finset.mem_insert]
                by_cases hyq' : y = q'
                · exact Or.inl hyq'
                · exact Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hyq', (Finset.mem_erase.mp hyin).2⟩)))
      · -- step: `s > J'`
        have hsJ' : t + 1 + j' < s := by omega
        have ih' := ih hsJ'
        have hds : repairSchedule e t q' (t + 1 + j') s = e s := by
          unfold repairSchedule
          simp [show s ≠ t by omega, show s ≠ t + 1 + j' by omega]
        change (if σ.getD s 0 ∈ schedCache e C₀ σ s then schedCache e C₀ σ s
            else insert (σ.getD s 0) ((schedCache e C₀ σ s).erase (e s))) ⊆
          (if σ.getD s 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s then
              schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
            else insert (σ.getD s 0) ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s).erase
              (repairSchedule e t q' (t + 1 + j') s)))
        rw [hds]
        intro x hx
        by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hr] at hx
          rw [if_pos (ih' hr)]
          exact ih' hx
        · rw [if_neg hr] at hx
          rcases Finset.mem_insert.mp hx with hxr | hxin
          · subst x
            by_cases hrE : σ.getD s 0 ∈
                schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
            · rw [if_pos hrE]
              exact hrE
            · rw [if_neg hrE]
              rw [Finset.mem_insert]
              left
              rfl
          · have hxE : x ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s :=
              ih' (Finset.mem_erase.mp hxin).2
            have hxne : x ≠ e s := (Finset.mem_erase.mp hxin).1
            by_cases hrE : σ.getD s 0 ∈
                schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
            · rw [if_pos hrE]
              exact hxE
            · rw [if_neg hrE]
              rw [Finset.mem_insert]
              right
              rw [Finset.mem_erase]
              constructor
              · exact hxne
              · exact hxE
/-- B2 analogue of the repair step: when `q = e t` is resident, at the first
disagreement replace `e`'s eviction with the policy's choice; the number of
misses increases by at most one, and agreement extends to `t + 1`. -/
lemma repair_step_swap (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hqin : e t ∈ schedCache e C₀ σ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = some j') :
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ ≤
      schedMisses e C₀ σ + 1 ∧
    agreeWithFIF (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ (t + 1) := by
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
  let q : Page := e t
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
  have hj : ∃ j, nextUse σ (t + 1) q = some j := by
    rcases hfifo with hnone | ⟨j, j0', hj, hj0', hjlt⟩
    · exfalso
      rw [hj'] at hnone
      contradiction
    · exact ⟨j, hj⟩
  rcases hj with ⟨j, hj⟩
  have hjj' : j < j' := by
    rcases hfifo with hnone | ⟨j0, j0', hj0, hj0', hjlt⟩
    · exfalso
      rw [hj'] at hnone
      contradiction
    · have hj0eq : j0 = j := Option.some.inj (hj0.symm.trans hj)
      have hj0'eq : j0' = j' := Option.some.inj (hj0'.symm.trans hj')
      omega
  constructor
  · -- misses:rF ≤ eF + 1 pointwise
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
          · -- s = J: request q, `e` faults
            subst s
            unfold rF eF r schedFaultAt
            have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
            have hqnotE : q ∉ schedCache e C₀ σ (t + 1 + j) := by
              exact swap_q_not_mem e σ C₀ hq hqin hft hj (by omega) le_rfl
            rw [hsig]
            rw [show (if t + 1 + j = t + 1 + j' then 1 else 0) = 0 by
              simp [show j ≠ j' by omega]]
            by_cases hr : q ∈ schedCache r C₀ σ (t + 1 + j)
            · rw [if_pos hr]
              rw [if_neg hqnotE]
              omega
            · rw [if_neg hr]
              rw [if_neg hqnotE]
          · -- t < s < J: inside the window, the request is neither q nor q'
            have hwin := repairSchedule_window_swap' e σ C₀ hC₀ ht hagree hdis hqin rfl hq hj hj' hjj'
              (s := s) (by omega) (by omega)
            unfold rF eF r schedFaultAt
            rcases hwin with hswap | hsub
            · -- Ŝ = insert q (E − q')
              rw [hswap]
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
            rcases hwin with hsub | ⟨x, hswap⟩
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
              rw [hswap]
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
            · -- s = J': rF ≤ eF + 1 is always true
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
    change (∑ s ∈ Finset.range σ.length, rF s) ≤ (∑ s ∈ Finset.range σ.length, eF s) + 1
    have hsum1 : (∑ s ∈ Finset.range σ.length, rF s) ≤
        ∑ s ∈ Finset.range σ.length, (eF s + (if s = t + 1 + j' then 1 else 0)) := by
      exact Finset.sum_le_sum (fun s hs => hper s (Finset.mem_range.mp hs))
    have hsum2 : (∑ s ∈ Finset.range σ.length, (eF s + (if s = t + 1 + j' then 1 else 0))) =
        (∑ s ∈ Finset.range σ.length, eF s) +
          ∑ s ∈ Finset.range σ.length, (if s = t + 1 + j' then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    have hsum3 : (∑ s ∈ Finset.range σ.length, (if s = t + 1 + j' then 1 else 0)) ≤ 1 := by
      rw [Finset.sum_ite_eq']
      by_cases hJ'in : t + 1 + j' ∈ Finset.range σ.length
      · simp [hJ'in]
      · simp [hJ'in]
    rw [hsum2] at hsum1
    exact le_trans hsum1 (Nat.add_le_add_left hsum3 _)
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
