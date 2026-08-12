import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B9_Assembly

/-
# Dev B10: case-one hdred supply

The case-one step (`iterate_main_case_one`) proves the OR-form
`e s ∈ E_s ∨ d s = q'` at exchange faults.  This file supplies the state's
`hdred` field: the branch-1 at-most-once machinery and the `hnb'`
construction for `CaseOneHdredHyp`.

Verified facts (Dev/search_caseone.py): the branch-1 spot
(exchange-fault ∧ `d s = q'`) is at most one, always a d-fault, and the
next disagreement after a case-one exchange lands exactly on it.

## The junk-position obstruction (verified 2026-08-12)

The `hdred` field is unbounded, but at positions `s ≥ σ.length` the
request is the junk page 0 (`σ.getD s 0 = 0`).  The at-most-once fails
there: a policy whose junk eviction is `q'` (reachable when `q' = 0`,
e.g. σ = [1,1,0,1,3], C₀ = {1,2}, t = 4) produces branch-1 spots at the
first junk positions.  The plain reducedness from a finite `hnb'` is
therefore NOT attainable; the field must be vacuous at junk:

- `case_one_junk_hit`: from position `σ.length + 2` on, the exchange's
  cache contains 0 (the first junk request at `σ.length + 1` loads it),
  so the exchange never faults there and `hdred` is vacuous;
- `case_one_hdred_supply` sets `hnb' = σ.length + 2` (the vacuous range)
  and proves `CaseOneHdredHyp`.

## The bounded at-most-once machinery (for the assembly)

The in-range positions `s < σ.length` are where the iteration actually
steps.  There:

- `case_one_D_minus_E_subset_q'`: `D_s − E_s ⊆ {q'}` — the exchange never
  gains a page `d` lacks except `q'`, so an exchange fault is a d-fault
  (`case_one_exchange_fault_imp_d_fault`);
- `case_one_branch1_once`: at most one branch-1 spot in `[t+1, σ.length)`
  (the `window_branch1_once` mechanism with `hnone` in place of `hj'`).

The assembly consequence (DESIGN.md "Case-one branch-1 verified"): the
next disagreement after a case-one exchange lands exactly on the branch-1
spot `s₁`, so with `hnb' = σ.length + 2` the next step is case B
(`t₂ < hnb'`) — the case-one step must absorb the branch-1 repair (the
repair evicts FIF's page at `s₁` and restores agreement at `s₁+1`), or a
no-window B-step construction is needed.
-/

namespace CLRS

namespace Caching

open Finset

/-- The request at position `s ≥ σ.length` is the junk page 0. -/
lemma getD_ge_length (σ : List Page) {s : ℕ} (hs : σ.length ≤ s) :
    σ.getD s 0 = 0 := by
  have hge := getD_drop σ 0 s 0
  rw [Nat.add_zero] at hge
  rw [← hge]
  have hdrop : σ.drop s = [] := List.drop_eq_nil_of_le hs
  simp [hdrop]

/-- `hnone` (`q'` never requested again) gives the bounded no-request fact
needed on `[t+1, σ.length)`. -/
lemma case_one_hq'ne_bounded (σ : List Page) (q' : Page) {t : ℕ}
    (hnone : nextUse σ (t + 1) q' = none) :
    ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q' := by
  have hnone' : ∀ q, q ∈ σ.drop (t + 1) → q ≠ q' := nextUse_eq_none_iff.mp hnone
  intro s hs1 hs2 h
  have hlt : s - (t + 1) < (σ.drop (t + 1)).length := by
    rw [List.length_drop]
    omega
  have hmem : σ.getD s 0 ∈ σ.drop (t + 1) := by
    have hge := getD_drop σ 0 (t + 1) (s - (t + 1))
    rw [Nat.add_sub_of_le hs1] at hge
    rw [← hge]
    rw [List.getD_eq_getElem _ 0 hlt]
    exact List.getElem_mem (l := σ.drop (t + 1)) hlt
  exact (hnone' (σ.getD s 0) hmem) h

/-- From position `σ.length + 2` on, the exchange's cache contains 0 (the
first junk request at `σ.length + 1` loads it), so the exchange never
faults there and `hdred` is vacuous. -/
lemma case_one_junk_hit (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (t : ℕ) (q q' : Page) :
    ∀ s, σ.length + 2 ≤ s →
      0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs
      by_cases hs' : σ.length + 2 ≤ s
      · have h0in : 0 ∈ schedCache e C₀ σ s := ih hs'
        rw [schedCache]
        by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hr]
          exact h0in
        · rw [if_neg hr]
          have hget : σ.getD s 0 = 0 := getD_ge_length σ (by omega)
          rw [hget]
          simp
      · -- base: s + 1 = σ.length + 2, i.e. the first junk step at index σ.length + 1
        have hs_eq : s = σ.length + 1 := by omega
        subst s
        rw [schedCache]
        have hget : σ.getD (σ.length + 1) 0 = 0 := getD_ge_length σ (by omega)
        rw [hget]
        by_cases hr : 0 ∈ schedCache e C₀ σ (σ.length + 1)
        · rw [if_pos hr]
          exact hr
        · rw [if_neg hr]
          simp

/-- At a d-fault inside the case-one window, the exchange evicts `q'`
(branch 1) or `d s` (branch 5 — `d s ∈ E_s` by the invariant and the
fault).  The branch-3/6 alternatives are excluded by the fault. -/
lemma case_one_exchange_decision_at_d_fault (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hs : t + 1 ≤ s) (hslen : s < σ.length)
    (hdF : σ.getD s 0 ∉ schedCache d C₀ σ s)
    (hA : schedCache d C₀ σ s \ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s ⊆ ({q'} : Finset Page)) :
    (d s = q' → exchangeSchedule d t q q' σ C₀ s = q') ∧
    (d s ≠ q' → exchangeSchedule d t q q' σ C₀ s = d s) := by
  have hdsD : d s ∈ schedCache d C₀ σ s := hdred s (by omega) hdF
  constructor
  · intro hd1
    unfold exchangeSchedule
    rw [exchangeScheduleCore_second]
    rw [← schedCache_exchangeScheduleCore]
    unfold exchangeDecision
    rw [if_neg (by omega), if_neg (by omega), if_pos hd1]
  · intro hd1
    have hdsE : d s ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
      by_contra hnot
      have hmem : d s ∈ schedCache d C₀ σ s \
          schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
        rw [Finset.mem_sdiff]
        exact ⟨hdsD, hnot⟩
      have hq'eq : d s = q' := Finset.mem_singleton.mp (hA hmem)
      exact hd1 hq'eq
    unfold exchangeSchedule
    rw [exchangeScheduleCore_second]
    rw [← schedCache_exchangeScheduleCore]
    unfold exchangeDecision
    rw [if_neg (by omega), if_neg (by omega), if_neg hd1]
    rw [if_neg (by intro h; exact hdF h.2)]
    rw [if_pos hdsE]

/-- The invariant `D_s − E_s ⊆ {q'}` over `[t+1, σ.length]`: the exchange
never gains a page `d` lacks except `q'`.  The d-hit case forces the
exchange hit (a d-hit exchange fault would put the request into
`D − E ⊆ {q'}` — a `q'` request); at double faults the exchange evicts
`q'` (branch 1) or `d s` (branch 5), both of which keep the diff inside
`{q'}`. -/
lemma case_one_D_minus_E_subset_q' (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hq'ne : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q') :
    ∀ s, t + 1 ≤ s → s ≤ σ.length →
      schedCache d C₀ σ s \ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s ⊆ ({q'} : Finset Page) := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs hslen
      by_cases hs' : t + 1 ≤ s
      · -- step: the invariant at s extends to s + 1
        have hih : schedCache d C₀ σ s \ schedCache e C₀ σ s ⊆ ({q'} : Finset Page) := ih hs' (by omega)
        intro x hx
        rw [Finset.mem_sdiff] at hx
        by_cases hdF : σ.getD s 0 ∉ schedCache d C₀ σ s
        · -- d faults at s
          by_cases heF : σ.getD s 0 ∉ schedCache e C₀ σ s
          · -- both fault: D and E both load r, d evicts d s, e evicts e s
            have hdec := case_one_exchange_decision_at_d_fault d t q q' σ C₀ hdred
              hs' (by omega) hdF (ih hs' (by omega))
            simp only [schedCache] at hx
            rw [if_neg hdF, if_neg heF] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE
            · exfalso
              exact hx.2 (Finset.mem_insert.mpr (Or.inl hxr))
            · have hxne_ds : x ≠ d s := (Finset.mem_erase.mp hxE).1
              have hxin : x ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hxE).2
              by_cases hxE2 : x ∈ schedCache e C₀ σ s
              · have hxnot : x ∉ (schedCache e C₀ σ s).erase (e s) := by
                  intro hm
                  exact hx.2 (Finset.mem_insert.mpr (Or.inr hm))
                have hxeq : x = e s := by
                  by_contra hne
                  exact hxnot (Finset.mem_erase.mpr ⟨hne, hxE2⟩)
                by_cases hd1 : d s = q'
                · rw [Finset.mem_singleton]
                  rw [hxeq]
                  exact hdec.1 hd1
                · exfalso
                  rw [hxeq] at hxne_ds
                  exact (hxne_ds (hdec.2 hd1)).elim
              · have hmem : x ∈ schedCache d C₀ σ s \ schedCache e C₀ σ s := by
                  rw [Finset.mem_sdiff]
                  exact ⟨hxin, hxE2⟩
                rw [Finset.mem_singleton]
                exact Finset.mem_singleton.mp (hih hmem)
          · -- exchange hits: E unchanged, D updates
            have hdsinE : σ.getD s 0 ∈ schedCache e C₀ σ s := by
              by_contra h
              exact heF h
            simp only [schedCache] at hx
            rw [if_neg hdF, if_pos hdsinE] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE
            · exfalso
              exact hx.2 (by rw [hxr]; exact hdsinE)
            · have hxne_ds : x ≠ d s := (Finset.mem_erase.mp hxE).1
              have hxin : x ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hxE).2
              have hmem : x ∈ schedCache d C₀ σ s \ schedCache e C₀ σ s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, hx.2⟩
              rw [Finset.mem_singleton]
              exact Finset.mem_singleton.mp (hih hmem)
        · -- d hits at s: the exchange must hit too, so both caches are unchanged
          have hin : σ.getD s 0 ∈ schedCache d C₀ σ s := by
            by_contra h
            exact hdF h
          have hinE : σ.getD s 0 ∈ schedCache e C₀ σ s := by
            by_contra h
            have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \ schedCache e C₀ σ s := by
              rw [Finset.mem_sdiff]
              exact ⟨hin, h⟩
            have hq'eq : σ.getD s 0 = q' := Finset.mem_singleton.mp (hih hmem)
            exact hq'ne s hs' (by omega) hq'eq
          simp only [schedCache] at hx
          rw [if_pos hin, if_pos hinE] at hx
          rw [Finset.mem_singleton]
          exact Finset.mem_singleton.mp (hih (Finset.mem_sdiff.mpr hx))
      · -- base: s + 1 = t + 1
        have hs_eq : s = t := by omega
        subst s
        have hE : schedCache e C₀ σ (t + 1) =
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
            insert (σ.getD t 0) ((schedCache d C₀ σ t).erase (d t)) := by
          rw [schedCache]
          rw [if_neg hft]
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [Finset.mem_singleton]
        rcases Finset.mem_insert.mp (by rw [← hD]; exact hx.1) with hxr | hxE
        · exfalso
          exact hx.2 (by rw [hE, hxr]; simp)
        · by_cases hxq' : x = q'
          · exact hxq'
          · exfalso
            have hxE' : x ∈ (schedCache d C₀ σ t).erase q' :=
              Finset.mem_erase.mpr ⟨hxq', (Finset.mem_erase.mp hxE).2⟩
            exact hx.2 (by rw [hE]; exact Finset.mem_insert.mpr (Or.inr hxE'))

/-- In `[t+1, σ.length)`, an exchange fault is a d-fault. -/
lemma case_one_exchange_fault_imp_d_fault (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hq'ne : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q')
    {s : ℕ} (hs : t + 1 ≤ s) (hslen : s < σ.length)
    (heF : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) :
    σ.getD s 0 ∉ schedCache d C₀ σ s := by
  intro h
  have hmem : σ.getD s 0 ∈ schedCache d C₀ σ s \
      schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
    rw [Finset.mem_sdiff]
    exact ⟨h, heF⟩
  have hq'eq : σ.getD s 0 = q' := Finset.mem_singleton.mp
    (case_one_D_minus_E_subset_q' d t q q' σ C₀ hft hdred hq'res hq'ne s hs (by omega) hmem)
  exact hq'ne s hs hslen hq'eq

/-- The branch-1 at-most-once over `[t+1, σ.length)`: two d-fault
positions with `d s = q'` contradict (the `window_branch1_once`
mechanism with `hnone` in place of the window bound). -/
lemma case_one_branch1_once (d : ℕ → Page) (t : ℕ) (q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hq'ne : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q')
    {s₁ : ℕ} (hs1 : t + 1 ≤ s₁) (hs1len : s₁ < σ.length)
    {s₂ : ℕ} (hs2lt : s₁ < s₂) (hs2len : s₂ < σ.length)
    (hbranch₁ : d s₁ = q') (hbranch₂ : d s₂ = q')
    (hFault₁ : σ.getD s₁ 0 ∉ schedCache d C₀ σ s₁)
    (hFault₂ : σ.getD s₂ 0 ∉ schedCache d C₀ σ s₂) :
    False := by
  have hq'in₂ : q' ∈ schedCache d C₀ σ s₂ := by
    exact hbranch₂ ▸ hdred s₂ (by omega) hFault₂
  -- q' ∈ cache s₂ 且 (s₁, s₂] 内无 q' 请求 ⟹ q' ∈ cache s₁(从未被真逐出)
  have hq'in₁ : q' ∈ schedCache d C₀ σ s₁ := by
    by_contra hnot
    have hqback : ∀ k, k ≤ s₂ → s₁ ≤ k → q' ∈ schedCache d C₀ σ k → q' ∈ schedCache d C₀ σ s₁ := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk2 hk1 hqk
          by_cases hk_eq : k = s₁
          · simpa [hk_eq] using hqk
          · have hk'1 : s₁ ≤ k - 1 := by omega
            have hk'2 : k - 1 ≤ s₂ := by omega
            have hqk' : q' ∈ schedCache d C₀ σ (k - 1) := by
              have hkeq : k = (k - 1) + 1 := by omega
              have hqk'' : q' ∈ schedCache d C₀ σ ((k - 1) + 1) := hkeq ▸ hqk
              rw [schedCache] at hqk''
              by_cases hr : σ.getD (k - 1) 0 ∈ schedCache d C₀ σ (k - 1)
              · rw [if_pos hr] at hqk''
                exact hqk''
              · rw [if_neg hr] at hqk''
                rcases Finset.mem_insert.mp hqk'' with hq'r | hq'E
                · exfalso
                  exact hq'ne (k - 1) (by omega) (by omega) hq'r.symm
                · exact (Finset.mem_erase.mp hq'E).2
            exact ih (k - 1) (by omega) hk'2 hk'1 hqk'
    exact hnot (hqback s₂ le_rfl (by omega) hq'in₂)
  -- s₁ 处真逐出(源 reduced ⟹ q' ∈ cache s₁、d s₁ = q')⟹ q' ∉ cache s₁+1
  have hq'out : q' ∉ schedCache d C₀ σ (s₁ + 1) := by
    rw [schedCache]
    rw [if_neg hFault₁]
    rw [hbranch₁]
    intro hm
    rcases Finset.mem_insert.mp hm with hq'r | hq'E
    · exfalso
      exact hq'ne s₁ hs1 hs1len hq'r.symm
    · exact (Finset.mem_erase.mp hq'E).1 rfl
  -- q' ∉ cache s₁+1 且 (s₁+1, s₂] 内无 q' 请求 ⟹ q' ∉ cache s₂ — 矛盾
  have hq'out₂ : q' ∉ schedCache d C₀ σ s₂ := by
    have hnoenter : ∀ k, s₁ + 1 ≤ k → k ≤ s₂ → q' ∉ schedCache d C₀ σ k := by
      intro k
      induction k with
      | zero => omega
      | succ k ih =>
          intro hk1 hk2
          by_cases hk1' : s₁ + 1 ≤ k
          · have hqnot : q' ∉ schedCache d C₀ σ k := ih hk1' (by omega)
            rw [schedCache]
            by_cases hr : σ.getD k 0 ∈ schedCache d C₀ σ k
            · rw [if_pos hr]
              exact hqnot
            · rw [if_neg hr]
              intro hm
              rcases Finset.mem_insert.mp hm with hq'r | hq'E
              · exfalso
                exact hq'ne k (by omega) (by omega) hq'r.symm
              · exact hqnot (Finset.mem_erase.mp hq'E).2
          · have hk1eq : k + 1 = s₁ + 1 := by omega
            simpa [hk1eq] using hq'out
    exact hnoenter s₂ (by omega) le_rfl
  exact hq'out₂ hq'in₂

/-- The case-one `hdred` supply: `hnb' = σ.length + 2`, where the field is
vacuous (the exchange's cache contains the junk request 0 from that
position on, so it never faults).  This instantiates `CaseOneHdredHyp`;
see the module doc for why no finite in-range bound is attainable. -/
lemma case_one_hdred_supply (σ : List Page) (C₀ : Finset Page) (M : ℕ) :
    CaseOneHdredHyp σ C₀ M := by
  intro st t ht hnb_le hagree hdis hnone
  let q : Page := st.d t
  let q' : Page := fifoSchedule σ C₀ t
  let e : ℕ → Page := exchangeSchedule st.d t q q' σ C₀
  refine ⟨σ.length + 2, by omega, ?_⟩
  intro s hs hfault
  have h0in : 0 ∈ schedCache e C₀ σ s := case_one_junk_hit st.d σ C₀ t q q' s hs
  have hget : σ.getD s 0 = 0 := getD_ge_length σ (by omega)
  exfalso
  exact hfault (by
    rw [hget]
    exact h0in)

end Caching

end CLRS
