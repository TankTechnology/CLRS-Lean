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
- `iterate_main_case_one`: the case-one (hAone) step — `q'` never
  requested again — the exchange extends agreement to `t + 1`, slack
  `+1` iff `q` is requested again (`exchangeSchedule_misses_le_plus_one`;
  `q` dead: misses equal by `exchangeSchedule_misses_eq_case_one`), and
  is reduced from `t + 1` on except the branch-1 positions (`d s = q'`
  — the exchange evicts `q'` as a no-op, not resident; at most one such
  fault); the q-dead sub-case's final agreement is attainable (the
  DESIGN's "unattainable" claim is stale — see `Dev/DESIGN.md`)
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

/-- Bridging lemma: the nop of the alive-alive repair `repairSchedule e t q'' (t + 1 + j'')`
occurs at `J'' = t + 1 + j''`, while `repair_cache_diff_le` is stated for the dead-page repair
`repairSchedule e t q'' t` (nop = `t`). Before `J = t + 1 + j`
(`j < j''`) the two schedules evict identically (both evict `q''` at `t`, both follow `e`
elsewhere, and the nop is not triggered), hence their caches agree. -/
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

/-- The window segment of an alive-alive B2 repair: for `J < s ≤ J''`, the repair's cache
differs from the source `e`'s cache only by missing `q''` (reverse diff `E − Ŝ ⊆ {q''}`).
At the base case `J + 1`, `e` faults at `J` and loads `q` (good event), `r` hits (`hkept`),
and in `E_J − Ŝ_J ⊆ {q, q''}` (`repair_cache_diff_le` at `J`) we have `q ∉ E_J`
(`swap_q_not_mem`), so only `q''` remains. The inductive step needs only `r s = e s`
(`s ∉ {t, J''}`) and `σ[s] ≠ q''`. -/
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
        -- base case: at J+1, e faults at J and loads q, r hits (cache unchanged)
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
        · -- x = q: contradicts q ∈ Ŝ_J (hkept)
          exfalso
          exact hxnotS (hxr ▸ hkept)
        · -- x ∈ E_J − e J, x ∉ Ŝ_J: E_J − Ŝ_J ⊆ {q, q''} (at J) and q ∉ E_J
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
      · -- inductive step: J < s
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
        · -- e hits ⟹ r hits (otherwise σ[s] ∈ E − Ŝ ⊆ {q''}, contradicting σ[s] = q'')
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
        · -- e faults
          rw [if_neg he] at hx
          by_cases hr' : σ.getD s 0 ∈ S s
          · -- r hits: Ŝ unchanged, E loads σ[s] and evicts e s
            rw [if_pos hr'] at hx
            rcases Finset.mem_insert.mp hx.1 with hxr | hxE2
            · exfalso
              exact hx.2 (hxr ▸ hr')
            · have hxin : x ∈ E s := (Finset.mem_erase.mp hxE2).2
              have hmem : x ∈ E s \ S s := by
                rw [Finset.mem_sdiff]
                exact ⟨hxin, hx.2⟩
              exact Finset.mem_singleton.mp (hih hmem)
          · -- double fault
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

/-- After `J''` of an alive-alive B2 repair: `E_s ⊆ Ŝ_s` (reverse diff empty). At the base
case `J'' + 1` both sides gain `q''` (e hits or loads, r loads — the nop evicting `q''` is a
no-op), and in `E_{J''} − Ŝ_{J''} ⊆ {q''}` (`hw` at `J''`) we have `q'' ∉ E − Ŝ` (both sides
have `q''`); the inductive step `r s = e s` preserves the containment. -/
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
        -- base case: at J''+1, request q''
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
          · -- double hit
            rw [hScase, if_pos hr']
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Finset.mem_sdiff] at hx
            have hmem : x ∈ E (t + 1 + j'') \ S (t + 1 + j'') := by
              rw [Finset.mem_sdiff]
              exact ⟨hx.1, hx.2⟩
            have hxq'' : x = q'' := Finset.mem_singleton.mp (hw (t + 1 + j'') (by omega) le_rfl hmem)
            exact hx.2 (hxq''.symm ▸ (hsig ▸ hr'))
          · -- e hits, r faults (nop evicts as a no-op, Ŝ loads q'')
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
        · -- e faults
          rw [hEcase, if_neg he]
          by_cases hr' : σ.getD (t + 1 + j'') 0 ∈ S (t + 1 + j'')
          · -- e faults, r hits
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
          · -- double fault
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
      · -- inductive step: J'' < s
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
        · -- e hits ⟹ r hits (E_s ⊆ Ŝ_s)
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
        · -- e faults
          rw [if_neg he] at hx
          by_cases hr' : σ.getD s 0 ∈ S s
          · -- r hits: Ŝ unchanged, E loads
            rw [if_pos hr'] at hx
            exact (Finset.notMem_empty x) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hx.2 (hxp.symm ▸ hr')
                · exact (Finset.mem_erase.mp hxE2).2, hx.2⟩))
          · -- double fault
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

/-- The full reverse diff of an alive-alive B2 repair: for `∀ s ≤ σ.length`, the repair's
cache differs from the source `e`'s cache only by pages in `{q, q''}`; for `J < s` it only
misses `q''`; for `J'' < s` it misses nothing (`E_s ⊆ Ŝ_s`). -/
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
  · -- s ≤ J: repair_cache_diff_le (constructing hdead)
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

/-- Reverse diff chain: the chain invariant `E − D ⊆ Q` (the reverse diff between the
reference schedule `e` and the iteration schedule `d`) is extended by only `q''` after the
alive-alive B2 repair `r = repairSchedule d t q'' (t + 1 + j'')`:
`E − Ŝ ⊆ insert q'' Q` holds for all `s ≤ σ.length`. Split `x ∈ E − Ŝ` according to
`x ∈ D` or not into the two branches `E − D ⊆ Q` (`hchain`) and `D − Ŝ ⊆ {q, q''}`
(`repair_diff_all`); `x = q` contradicts `q ∉ E` (`hqnotE`, since `e` evicts `q` at `t`
over the window `(t, J]`), so only `q''` remains. -/
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
  · -- s ≤ t: r and d have the same cache (S = D), so x ∉ S ⟹ x ∉ D ⟹ x ∈ E − D ⊆ Q
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
    · -- x ∈ D: x ∈ D − Ŝ ⊆ {q, q''} (or {q''} within the window)
      have hmem : x ∈ D s \ S s := by
        rw [Finset.mem_sdiff]
        exact ⟨hxD, hx.2⟩
      by_cases hsJ : s ≤ t + 1 + j
      · -- s ≤ J: ⊆ {q, q''}; x = q contradicts q ∉ E
        rw [Finset.mem_insert]
        have hxqq'' := (hdiff s hslen).1 hmem
        rcases Finset.mem_insert.mp hxqq'' with hxq | hxq''
        · exfalso
          exact hqnotE s hts hsJ (hxq ▸ hx.1)
        · exact Or.inl (Finset.mem_singleton.mp hxq'')
      · -- J < s: ⊆ {q''} within the window, empty after J''
        have hsJ' : t + 1 + j < s := by omega
        by_cases hsJ'' : s ≤ t + 1 + j''
        · rw [Finset.mem_insert]
          have hxq'' := Finset.mem_singleton.mp ((hdiff s hslen).2.1 hsJ' hmem)
          exact Or.inl hxq''
        · have hsJ'' : t + 1 + j'' < s := by omega
          exfalso
          exact (Finset.notMem_empty x) ((hdiff s hslen).2.2 hsJ'' ▸ hmem)
    · -- x ∉ D: x ∈ E − D ⊆ Q
      rw [Finset.mem_insert]
      exact Or.inr (hchain s hslen (by
        rw [Finset.mem_sdiff]
        exact ⟨hx.1, hxD⟩))

/-- Reverse diff chain (dead-q'' version): after a B2 repair
`r = repairSchedule d t q'' t` where `q''` is never requested again, the chain invariant
`E − D ⊆ Q` is extended by only `q''`. Isomorphic to `reverse_diff_chain`, but the difference
sets use the dead-page lemmas: at `s ≤ J` use `repair_cache_diff_le`
(`D − Ŝ ⊆ {q, q''}`, with `x = q` contradicting `hqnotE`), and after `J` use
`repair_cache_diff_after` (`D − Ŝ ⊆ {q''}`, no longer needing to exclude `q`). -/
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
  · -- s ≤ t: r and d have the same cache (S = D), so x ∉ S ⟹ x ∉ D ⟹ x ∈ E − D ⊆ Q
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
    · -- s ≤ J: x ∈ D − Ŝ ⊆ {q, q''}, x = q contradicts hqnotE
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
      · -- x ∉ D: x ∈ E − D ⊆ Q
        rw [Finset.mem_insert]
        exact Or.inr (hchain s hslen (by
          rw [Finset.mem_sdiff]
          exact ⟨hx.1, hxD⟩))
    · -- J < s: D − Ŝ ⊆ {q''}
      have hsJ' : t + 1 + j < s := by omega
      by_cases hxD : x ∈ D s
      · have hmem : x ∈ D s \ S s := by
          rw [Finset.mem_sdiff]
          exact ⟨hxD, hx.2⟩
        rw [Finset.mem_insert]
        exact Or.inl (Finset.mem_singleton.mp (hdiff_after s hsJ' hslen hmem))
      · -- x ∉ D: x ∈ E − D ⊆ Q
        rw [Finset.mem_insert]
        exact Or.inr (hchain s hslen (by
          rw [Finset.mem_sdiff]
          exact ⟨hx.1, hxD⟩))

/-- Reverse diff chain (dead-q version): after a B2 repair
`r = repairSchedule d t q'' t` where both `q` and `q''` are never requested again, the chain
invariant `E − D ⊆ Q` is extended by only `q''`. `D − Ŝ ⊆ {q, q''}` holds everywhere
(`repair_cache_diff`, with unbounded `hdead`), and `x = q` contradicts `hqnotE` (which the
caller obtains from `swap_q_not_mem_dead`). -/
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
  · -- s ≤ t: r and d have the same cache (S = D), so x ∉ S ⟹ x ∉ D ⟹ x ∈ E − D ⊆ Q
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
    · -- x ∈ D: x ∈ D − Ŝ ⊆ {q, q''}, x = q contradicts hqnotE
      have hmem : x ∈ D s \ S s := by
        rw [Finset.mem_sdiff]
        exact ⟨hxD, hx.2⟩
      rw [Finset.mem_insert]
      have hxqq'' := (hdiff s hslen).2 hmem
      rcases Finset.mem_insert.mp hxqq'' with hxq | hxq''
      · exfalso
        exact hqnotE s hts hslen (hxq ▸ hx.1)
      · exact Or.inl (Finset.mem_singleton.mp hxq'')
    · -- x ∉ D: x ∈ E − D ⊆ Q
      rw [Finset.mem_insert]
      exact Or.inr (hchain s hslen (by
        rw [Finset.mem_sdiff]
        exact ⟨hx.1, hxD⟩))

/-- The B2 e-hit lemma (single-step local form, in the style of the Huffman exchange
argument): at a disagreement position `t`, if `d` faults (`hft`) and the instance of the
reverse-diff chain at `t`, `E_t − D_t ⊆ Q` (`hchain`, given pointwise by
`reverse_diff_chain`), holds, then a request `σ[t]` that hits the reference schedule `e`'s
cache is forced into `Q`: `σ[t] ∈ E_t ⟹ σ[t] ∈ Q`. This is the first step of the b2_ehit
mechanism in DESIGN — it performs only the local single step at position `t`, not the global
`Q''` tracking (the chain invariant encapsulates the global part). The contradiction of
`σ[t] ∈ Q` with "dead page or not yet requested" is handled by `b2_ehit_ne`. Empirical
verification: search3 of search_iter.py reports e-hit = 0 across 55188 B2 positions. -/
lemma b2_ehit (e d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (Q : Finset Page)
    (hchain : schedCache e C₀ σ t \ schedCache d C₀ σ t ⊆ Q) :
    σ.getD t 0 ∈ schedCache e C₀ σ t → σ.getD t 0 ∈ Q := by
  intro he
  exact hchain (by
    rw [Finset.mem_sdiff]
    exact ⟨he, hft⟩)

/-- The contradiction half of the B2 e-hit lemma: when every `q''ᵢ` in the set of past
repair pairs `Q ⊆ ℕ × Page` (elements `(tᵢ, q''ᵢ)`, repair position and repair page) is
either a dead page (`nextUse σ (tᵢ+1) q''ᵢ = none`) or not yet requested at `t`
(`t < tᵢ + 1 + j''ᵢ`), the request `σ[t]` is not among the pages of `Q`:
`σ[t] ∉ Q.image Prod.snd`. Dead pages use `getD_ne_of_nextUse_none` (B6), not-yet-requested
pages use `getD_ne_nextUse`. Empirical verification: at disagreement positions the request
belongs to a past repair page 8976 times, all at `t = J''ᵢ` (B1 nop positions), and 0 times
on B2 — this lemma covers the dead-page and `t < J''ᵢ` branches, leaving the `t = J''ᵢ`
branch (B1 rather than B2) to `iterate_main`. -/
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
  · -- dead page: σ[t] = q'' contradicts `q''` never being requested after tᵢ
    exact getD_ne_of_nextUse_none σ hdead (by omega) ht hsigq.symm
  · -- not yet requested: requesting σ[t] = q'' at t < J''ᵢ contradicts the first request at J''ᵢ
    exact getD_ne_nextUse (k := t) hnext (by omega) htltJ hsigq.symm

/-- The keep-swap core (the current schedule's `b2_no_evict_q`): within the window
`(t, J]` of a B2 position `t`, for every fault position `s` of `e`:
- `d s = e s` — position `s` is not a past repair/nop position (`hnot`, recorded by `P`;
  the composition invariant `hd_eq` gives eviction agreement off `P`). Empirically, 136
  windows have past repair/nop positions inside `(t, J]`, and among them 12 are faults of
  `e` with `d s ≠ e s`, so `hnot` is essential;
- `e s ≠ q` — an instantiation of `exchange_no_evict_q`, whose `hft₂` (e faults at `t`)
  is derived from `b2_ehit` (the instance of the chain `hchain` at `t` forces `σ[t] ∈ E_t`
  into `Q.image Prod.snd`) plus `b2_ehit_ne` (the dead-page-or-not-requested contradiction);
  `hqin` (`q ∈ E_t`) comes from the branch analysis of `e t = q` (supplied by the caller). -/
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

/-- The keep-swap form for B2 (current window): the B6 `repair_keep_swap` instantiated in
the iteration context — the window parameters `(t₀, q₀, q₀', j₀')` together with the local
facts at the B2 position `t` (`hagree`/`hdis` from the window version of `first_disagree`,
`hqin` is the B2 residency, `hj`/`hj''`/`hjj''` the alive-alive situation) give the swap
form at the good event `J = t + 1 + j`:
`Ŝ_J = insert q (E_J − q'')`. Merely an instantiation, no new proof. -/
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

/-- The keep-swap form for B2 (dead-q'' version): the B6 `repair_keep_swap_qp_dead`
instantiated in the iteration context — when `q''` is never requested again, the dead-page
repair `r = repairSchedule e t q'' t` still has the swap form
`Ŝ_J = insert q (E_J − q'')` at the good event `J = t + 1 + j`
(giving the `q ∈ Ŝ_J` needed by `repair_step_swap_qp_dead`). Merely an instantiation, no new proof. -/
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

/-- The keep-swap derivation (current-schedule version): the repair at the B2 position `t₂`
acts on the **current** schedule `d` (the exchange schedule `e = exchangeSchedule d_pre t₀
q₀ q₀' σ C₀` plus past repairs), rather than on the bare exchange schedule. The swap form
`Ŝ = insert q (D − q'')` is maintained on `(t₂, J]` (in particular up to `J` — the good
event). Isomorphic to `repair_keep_swap`, but `d s ≠ q` is given by `hd_eq` (`d = e` off `P`)
plus `hnot` (no past modification positions in the window) plus `exchange_no_evict_q`;
`e` faults at `t₂` is derived from the chain `hchain` via `b2_ehit` + `b2_ehit_ne`;
the `e` faults within the window (`σ[s] ∉ E_s`) are given by `hnotE` (the Q''-exclusion
argument, see DESIGN); `hqinE` (`q` in the exchange schedule's cache at `t₂`) is the branch
analysis (see the `b2_no_evict_q` comment). -/
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
          · -- r hits ⟹ d hits, both caches unchanged, the form is preserved
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
            -- the three cases for d s
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
              · -- d s = q'': both erases are no-ops
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
              · -- d s ∉ {q, q''}: the erases commute, the form is preserved
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

/-- The keep-swap derivation (current-schedule dead-q'' version): at a B2 position `t₂`
where `q''` is never requested again, the dead-page repair `r = repairSchedule d t₂ q'' t₂`
maintains the swap form `Ŝ = insert q (D − q'')` on `(t₂, J]` (in particular up to `J` —
the good event, giving `reverse_diff_chain_qp_dead`'s `hkept`). Isomorphic to
`repair_keep_swap_cur`: `d s ≠ q` is given by `hd_eq` (`d = e` off `P`) plus `hnot` (no past
modification positions in the window) plus `exchange_no_evict_q`; `e` faults at `t₂` is
derived from the chain `hchain` via `b2_ehit` + `b2_ehit_ne`; the `e` faults within the
window (`σ[s] ∉ E_s`) are given by `hnotE`. Requests avoiding `q''` are given by `hq''dead`
(`getD_ne_of_nextUse_none`, needing `hJlen`) rather than `hj''`, and the nop is changed from
`t₂ + 1 + j''` to `t₂` (base case `repairSchedule_base_swap_qp_dead`). -/
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
          · -- r hits ⟹ d hits, both caches unchanged, the form is preserved
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
            -- the three cases for d s
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
              · -- d s = q'': both erases are no-ops
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
              · -- d s ∉ {q, q''}: the erases commute, the form is preserved
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

/-- The absence of `q''` in a B1 repair: `q''` is evicted by the repair at `t`, and does
not return to the repair's cache before `J''' = t + 1 + j'''` (requests avoid `q''`, and the
repair only inserts `σ[s]`). The repair analogue of `swap_q_not_mem`. -/
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

/-- After `J'''` of a B1 repair: the reverse diff is empty (`E − Ŝ = ∅`; the superset
direction is given by `repairSchedule_superset`). At the base case `J''' + 1`: `r` faults at
`J'''` and loads `q''` (`hq''notS`, the nop evicting `q''` is a no-op), and `e` either hits
or loads — in both cases the residual `q''` of `E − Ŝ ⊆ {q''}` (`hwin` at `J'''`) is already
in `Ŝ'`; the inductive step `r s = e s` preserves the empty difference (`e` hits ⟹ `r`
hits, and the remaining cases are excluded element by element). -/
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
        -- base case: at J'''+1, request q''
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
        · -- e hits: cache unchanged
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
        · -- e faults: loads q''
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
      · -- inductive step: J''' < s
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
        · -- e hits ⟹ r hits (E − Ŝ = ∅)
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
        · -- e faults
          rw [if_neg he] at hx
          by_cases hr' : σ.getD s 0 ∈ S s
          · -- r hits: Ŝ unchanged, E loads
            rw [if_pos hr'] at hx
            exact (Finset.notMem_empty x) (hih ▸ (by
              rw [Finset.mem_sdiff]
              exact ⟨by
                rcases Finset.mem_insert.mp hx.1 with hxp | hxE2
                · exfalso
                  exact hx.2 (hxp.symm ▸ hr')
                · exact (Finset.mem_erase.mp hxE2).2, hx.2⟩))
          · -- double fault
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

/-- Branch analysis: at a fault of the exchange after `t` (within the window), the eviction
`e s` is `q'` or resident (`e s ∈ E_s ∪ {q'}`). The structure of `exchangeDecision`: branch 1
evicts `q'`; branches 4-6 evict a page of `E − D` or `d s ∈ E_s`; the `else 0` when `M` is
empty is excluded by faulting plus the cardinality argument (`exchangeScheduleCore_card`).
This is the mechanism behind `hqinE` (`q ∈ E_{t₂}` at B2 — the `q'` branch is B1) and "the
exchange never evicts a past `q''ᵢ`". -/
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

/-- The no-nop-at-B2 derivation (core of the last-repair analysis): `P` is the set of past
repair positions (`tᵢ` and the nop `tᵢ + 1 + j''ᵢ` of a live pair), `hcomp` is the value
invariant — the value at each position of `P` is the page of some pair (`s = tᵢ` or
`s = nᵢ` with `d s = q''`), and `hpair` gives the past facts of each pair at its `tᵢ`
(`σ[tᵢ]` faults, `q''` resident, `d tᵢ = q''`, maintained after the repair). At a B2
position `t` (`d t ∈ D_t`): if `t ∈ P`, then `t = tᵢ` (`hpast` contradiction) or `t = nᵢ` —
the value invariant gives `d t = q''`, while
`evicted_page_absent_until_request` (absent after eviction until requested) gives
`q'' ∉ D_t`, contradicting `d t ∈ D_t`. -/
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
  · -- t = tᵢ: contradicts tᵢ < t
    have hlt : tᵢ < t := hpast tᵢ q'' htq
    omega
  · -- t = nᵢ: the value invariant gives d t = q'' (for some pair), while q'' ∉ D_t (absent after eviction until requested)
    rcases hcomp t htP with hc1 | hc2
    · -- t is also some pair's tᵢ: hpast contradiction
      rcases hc1 with ⟨tₗ, qₗ, htqₗ, hteqₗ, hdtₗ⟩
      have hlt : tₗ < t := hpast tₗ qₗ htqₗ
      omega
    · -- t = nₗ and d t = qₗ: evicted_page_absent_until_request
      rcases hc2 with ⟨tₗ, qₗ, jₗ, htqₗ, hnextₗ, hteqₗ, hdtₗ⟩
      rcases hpair tₗ qₗ jₗ htqₗ hnextₗ with ⟨hftₗ, hqresₗ, hdtₗ'⟩
      have habs : qₗ ∉ schedCache d C₀ σ (tₗ + 1 + jₗ) :=
        evicted_page_absent_until_request d σ C₀ tₗ qₗ hftₗ hqresₗ hdtₗ' hnextₗ
      have : qₗ ∉ schedCache d C₀ σ t := by
        rwa [hteqₗ]
      exact this (hdtₗ ▸ hqin)

/- ### Extension glue for the case steps (hpast/hQfifo/hP/hP_in/hcomp/hpair)

The new state of a case B1/B2 step carries `Q' = insert (t₂, q'') Q` and
`P' = P ∪ {t₂, nop}` (for a live pair, nop = `t₂ + 1 + j''`; for a dead-page repair,
nop = `t₂`, i.e. `P' = P ∪ {t₂}`). The extension lemmas below carry the composition
invariant family of the old state (see `IterateState`) to the new state: old positions are
witnessed by the old invariants (`r` and `d` agree off `{t₂, nop}`, caches agree at
`tᵢ ≤ t₂`), and the new positions/new pair are witnessed by the facts of the case step
itself (`r t₂ = q''`, `r nop = q''`, `σ[t₂]` faults, `q''` resident). The extension of hQ is
a legacy blocker (see DESIGN: the strict bound `t₂ + 1 < J''ᵢ` does not hold for old pairs
over the full historical Q). -/

/-- hpast extension: after the new pair `(t₂, q'')` is added to Q, every pair's repair
position `tᵢ` is strictly before the new bound `t₂ + 1` (old pairs by `hpast`, the new pair
since `t₂ < t₂ + 1`). -/
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

/-- hQfifo extension: the page of the new pair `(t₂, q'')` is exactly FIF's eviction at
`t₂` (`hq''`), and old pairs are handled by `hQfifo`. -/
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

/-- hQ extension: the per-pair clause of `Q' = insert (t₂, q'') Q` at the new bound `t₂+1`.
Old pairs reuse `hQ` (the caller supplies the strengthened bound `t₂+1 < nᵢ` — for the B2
step from `past_pair_first_request_after` plus the boundary case, see DESIGN "hQ-extension
blocker"); the clause for the new pair `(t₂, q'')` needs `0 < j''` (the nop `t₂+1+j''` is
strictly after the new bound `t₂+1`). -/
lemma extend_hQ (σ : List Page) (C₀ : Finset Page) (Q : Finset (ℕ × Page))
    {t₂ : ℕ} {q'' : Page}
    (hQ : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j''₀, nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ t₂ + 1 < tᵢ + 1 + j''₀)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) q'' = some j'') (hj''0 : 0 < j'') :
    ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j''₀, nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ t₂ + 1 < tᵢ + 1 + j''₀ := by
  intro tᵢ q''₀ htq
  rw [Finset.mem_insert] at htq
  rcases htq with hEq | htq
  · rcases hEq with ⟨rfl, rfl⟩
    right
    refine ⟨j'', hj'', ?_⟩
    omega
  · exact hQ tᵢ q''₀ htq

/-- Per-page credit (the hQ supply for the B2 step): at the B2 disagreement `t₂`, the
strengthened bound `t₂ < nᵢ` for old pairs is given by `past_pair_first_request_after` from
the old `hQ₀` (old bound `t0`); `0 < j''` is given by `getD_eq_nextUse` together with
`hnotE` (the exchange faults at `t₂+1`) and `q'' ∈ E_{t₂+1}` (resident plus the reverse-diff
chain) — a global argument, see the `0 < j''` boundary case of DESIGN "hQ-extension
blocker". -/
lemma b2_hQ_j''_pos (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (d : ℕ → Page) (t₂ : ℕ) (ht₂ : t₂ < σ.length)
    (hftd : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    {q'' : Page} (hq'' : q'' = fifoSchedule σ C₀ t₂)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) q'' = some j'')
    (hq''res : q'' ∈ schedCache (exchangeSchedule d (t₂ - 1) (d (t₂ - 1)) q'' σ C₀) C₀ σ (t₂ + 1))
    (hnotE : σ.getD (t₂ + 1) 0 ∉ schedCache (exchangeSchedule d (t₂ - 1) (d (t₂ - 1)) q'' σ C₀) C₀ σ (t₂ + 1)) :
    0 < j'' := by
  by_contra h0
  have hj''0 : j'' = 0 := by omega
  have hsig : σ.getD (t₂ + 1) 0 = q'' := by
    have hge := getD_eq_nextUse hj''
    rw [hj''0] at hge
    simpa using hge
  exact hnotE (hsig ▸ hq''res)

/-- hP extension (live-pair version): `P' = P ∪ {t₂, t₂+1+j''}`. Old positions reuse the old
`hP` (their witnessing pair is still in `Q'`), and the new position `t₂` and the new nop
`J'' = t₂+1+j''` are witnessed by the new pair `(t₂, q'')` (the `s = tᵢ` and
`s = tᵢ+1+j''` cases). -/
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

/-- The converse of hP (live-pair version): positions witnessed by new/old pairs all lie in
`P ∪ {t₂, J''}`. The `j''₀` witnessing the nop of the new pair `(t₂, q'')` equals `j''` by
the uniqueness of nextUse; `hpast` excludes `(t₂, q''₀) ∈ Q` (old pairs have position
`tᵢ ≠ t₂`). -/
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

/-- hcomp extension (live-pair version): the value invariant of the new schedule `r` over
`P' = P ∪ {t₂, J''}`. Old positions (≠ the new nop) reuse the old `hcomp` (`r s = d s`);
`t₂` and the new nop are witnessed by the new pair `(t₂, q'')` (`r` evicts `q''` at `t₂` and
`J''` — when the new nop covers an old position, the new witness still holds). -/
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

/-- hcomp extension (dead-page B1 version, without the `ht₂notP` hypothesis): like
`extend_hcomp'`, for the dead-page repair `P' = P ∪ {t₂}`. -/
lemma extend_hcomp_dead' (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (r d : ℕ → Page) {t₂ : ℕ} {q'' : Page}
    (hrt : r t₂ = q'')
    (hre : ∀ s, s ≠ t₂ → r s = d s)
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
  · by_cases hs₂ : s = t₂
    · subst s
      left
      refine ⟨t₂, q'', Finset.mem_insert_self _ _, rfl, hrt⟩
    · rcases hcomp s hsP with h1 | h2
      · rcases h1 with ⟨tᵢ, q''₀, htq, hteq, hds⟩
        left
        refine ⟨tᵢ, q''₀, ?_, hteq, ?_⟩
        · exact Finset.mem_insert.mpr (Or.inr htq)
        · rw [hre s hs₂]
          exact hds
      · rcases h2 with ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq, hds⟩
        right
        refine ⟨tᵢ, q''₀, j''₀, ?_, hnext₀, hteq, ?_⟩
        · exact Finset.mem_insert.mpr (Or.inr htq)
        · rw [hre s hs₂]
          exact hds
  · rw [Finset.mem_singleton] at hsNew
    subst s
    left
    refine ⟨t₂, q'', Finset.mem_insert_self _ _, rfl, hrt⟩

/-- hcomp extension (B1 version, without the `ht₂notP` hypothesis): when `t₂ ∈ P` (a B1
position may be a past nop position), the `by_cases s = t₂` routes `s = t₂` to the new
pair's witness. -/
lemma extend_hcomp' (σ : List Page) (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (r d : ℕ → Page) {t₂ : ℕ} {q'' : Page}
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) q'' = some j'')
    (hrt : r t₂ = q'') (hrN : r (t₂ + 1 + j'') = q'')
    (hre : ∀ s, s ∉ ({t₂, t₂ + 1 + j''} : Finset ℕ) → r s = d s)
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
  · by_cases hs₂ : s = t₂
    · -- s = t₂ ∈ P: witnessed by the new pair
      subst s
      left
      refine ⟨t₂, q'', Finset.mem_insert_self _ _, rfl, hrt⟩
    · by_cases hsN : s = t₂ + 1 + j''
      · -- s = J'' ∈ P: witnessed by the new pair
        subst s
        right
        refine ⟨t₂, q'', j'', Finset.mem_insert_self _ _, hj'', rfl, hrN⟩
      · rcases hcomp s hsP with h1 | h2
        · rcases h1 with ⟨tᵢ, q''₀, htq, hteq, hds⟩
          left
          refine ⟨tᵢ, q''₀, ?_, hteq, ?_⟩
          · exact Finset.mem_insert.mpr (Or.inr htq)
          · rw [hre s (by
              intro hmem
              rw [Finset.mem_insert] at hmem
              rcases hmem with hEq | hmem
              · exact hs₂ hEq
              · exact hsN (Finset.mem_singleton.mp hmem))]
            exact hds
        · rcases h2 with ⟨tᵢ, q''₀, j''₀, htq, hnext₀, hteq, hds⟩
          right
          refine ⟨tᵢ, q''₀, j''₀, ?_, hnext₀, hteq, ?_⟩
          · exact Finset.mem_insert.mpr (Or.inr htq)
          · rw [hre s (by
              intro hmem
              rw [Finset.mem_insert] at hmem
              rcases hmem with hEq | hmem
              · exact hs₂ hEq
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

/-- hpair extension: the past facts of the new pair `(t₂, q'')` (`σ[t₂]` faults, `q''`
resident, `r t₂ = q''`), and those of old pairs (`r`'s cache agrees with `d` at `tᵢ ≤ t₂`,
`r tᵢ = d tᵢ`, transported from `hpair`). -/
lemma extend_hpair (σ : List Page) (C₀ : Finset Page) (Q : Finset (ℕ × Page))
    (r d : ℕ → Page) {t₂ : ℕ} {q'' : Page}
    (hft : σ.getD t₂ 0 ∉ schedCache d C₀ σ t₂)
    (hq''in : q'' ∈ schedCache d C₀ σ t₂)
    (hrt : r t₂ = q'')
    (hre : ∀ s, s < t₂ → r s = d s)
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
    · rw [hre tᵢ htᵢlt]
      exact hdtᵢ

/-- hP extension (dead-page version): `P' = P ∪ {t₂}` (a dead-page repair has no nop
position). -/
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

/-- The converse of hP (dead-page version): the new pair `(t₂, q'')` is dead
(`nextUse = none`), so its nop witness is impossible and only `s = t₂` witnesses it. -/
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

/-- hcomp extension (dead-page version): `P' = P ∪ {t₂}`; `t₂` is witnessed by the new pair
(`r t₂ = q''`), and old positions reuse the old `hcomp` via `r s = d s`. -/
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

/-- Case B1 of the iteration (alive subcase): at a no-op disagreement `t₂` in the window
(`d t₂ ∉ cache`), when `q''` will be requested again (`hj'''`), the repair
`r = repairSchedule d t₂ q'' (t₂ + 1 + j''')` satisfies: agreement up to `t₂ + 1`
(`repair_step`); exact miss accounting — `rF ≤ eF` everywhere, and at `J'''` `rF = 1` while
`eF = 1 − bad` (bad event `bad = σ[J'''] ∈ D_{J'''}`), hence
`schedMisses r ≤ schedMisses d + bad` (the slack bookkeeping `slack − bad`);
the reverse-diff chain extends by `insert q'' (Q.image Prod.snd)`
(`repair_diff_noop_window` + `repair_reverse_diff_after_nop`, the latter's superset
direction supplied by `repairSchedule_superset`); `hd_eq` extends to `P ∪ {t₂, J'''}`;
the reducedness bound `max hnb (J''' + 1)` (`repairSchedule_superset`). -/
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
        σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s) ∧
      r t₂ = fifoSchedule σ C₀ t₂ ∧
      r (t₂ + 1 + j''') = fifoSchedule σ C₀ t₂ ∧
      (∀ s, s ∉ ({t₂, t₂ + 1 + j'''} : Finset ℕ) → r s = d s) ∧
      (∀ s, s ≤ t₂ → schedCache r C₀ σ s = schedCache d C₀ σ s) := by
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
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- agreement up to t₂+1
    exact (repair_step d σ C₀ hC₀ ht₂ hagree hdis hnoop hj''').2
  · -- miss accounting: schedMisses r ≤ schedMisses d + bad
    have hpoint_le : ∀ s, s < σ.length → s ≠ t₂ + 1 + j''' →
        schedFaultAt r C₀ σ s ≤ schedFaultAt d C₀ σ s := by
      intro s hs hsne
      unfold schedFaultAt
      by_cases hs_le_t : s ≤ t₂
      · -- caches equal
        rw [hce s hs_le_t]
      · by_cases hsJ : s ≤ t₂ + 1 + j'''
        · -- t₂ < s < J''': hits/faults aligned (window difference)
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
        · -- s > J''': D − Ŝ = ∅ ⟹ e hits ⟹ r hits
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
    · -- bad event: Σ rF ≤ Σ eF + 1
      rw [if_pos hbad]
      have heFJ : schedFaultAt d C₀ σ (t₂ + 1 + j''') = 0 := by
        unfold schedFaultAt
        rw [hsig]
        rw [if_pos (by rwa [← hsig])]
      rw [← hsum_erase_r]
      have h' := hsum_erase_d
      rw [heFJ] at h'
      omega
    · -- no bad event: Σ rF ≤ Σ eF (at J''' rF = eF = 1)
      rw [if_neg hbad]
      have heFJ : schedFaultAt d C₀ σ (t₂ + 1 + j''') = 1 := by
        unfold schedFaultAt
        rw [hsig]
        rw [if_neg (by rwa [← hsig])]
      rw [← hsum_erase_r]
      have h' := hsum_erase_d
      rw [heFJ] at h'
      omega
  · -- chain extends to insert q'' (Q.image Prod.snd)
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
    · -- s > J''': D − Ŝ = ∅; x ∈ D contradicts, x ∉ D goes through the chain
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
  · -- hd_eq extends to P ∪ {t₂, J'''}
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
  · -- reducedness bound: max hnb (J'''+1)
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
  · -- r t₂ = q''
    simpa [q''] using repairSchedule_at_t d t₂ q'' (t₂ + 1 + j''')
  · -- r J''' = q''
    unfold r repairSchedule
    simp [q'']
  · -- r s = d s off {t₂, J'''}
    intro s hs
    unfold r repairSchedule
    simp [show s ≠ t₂ by (intro h; exact hs (by simp [h])),
      show s ≠ t₂ + 1 + j''' by (intro h; exact hs (by simp [h]))]
  · -- caches agree up to t₂
    exact hce

/-- Case B2 of the iteration (alive-alive subcase): at a resident disagreement `t₂` in the
window (`d t₂` is in `d`'s cache, both `q` and `q''` will be requested again, `j < j''`),
the repair `r = repairSchedule d t₂ q'' (t₂ + 1 + j'')` satisfies:
- agreement up to `t₂ + 1` and misses not increased (`repair_step_swap_strong`, with the
  swap form given by `repair_keep_swap_cur`);
- the reverse-diff chain extends to `insert q'' (Q.image Prod.snd)` (`reverse_diff_chain`);
- the composition invariant `hd_eq` extends to `P ∪ {t₂, t₂ + 1 + j''}` (`r` changes only
  these two positions);
- the reducedness bound rises to `max hnb (t₂ + 1 + j'' + 1)`
  (`repairSchedule_superset_swap`: after `J''`, `D ⊆ Ŝ`, so at `r`'s faults `d` also
  faults, and `r s = d s ∈ D ⊆ Ŝ`).
`hqinE`, `hnotE`, `hnot`, `ht₂notP` are supplied by the inductive caller (branch analysis,
the Q''-exclusion and no-nop-at-B2 arguments, see DESIGN). -/
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
        σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s) ∧
      r t₂ = fifoSchedule σ C₀ t₂ ∧
      r (t₂ + 1 + j'') = fifoSchedule σ C₀ t₂ ∧
      (∀ s, s ∉ ({t₂, t₂ + 1 + j''} : Finset ℕ) → r s = d s) ∧
      (∀ s, s ≤ t₂ → schedCache r C₀ σ s = schedCache d C₀ σ s) := by
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
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- agreement up to t₂+1
    exact (repair_step_swap_strong d σ C₀ hC₀ ht₂ hagree hdis hqin hj hj'' hjj'' hswap).2
  · -- misses not increased
    exact (repair_step_swap_strong d σ C₀ hC₀ ht₂ hagree hdis hqin hj hj'' hjj'' hswap).1
  · -- chain extends to insert q'' (Q.image Prod.snd)
    exact reverse_diff_chain e d σ C₀ (show d t₂ = q from rfl) rfl hqin hftd hqq'' hj hj'' hjj''
      hkept (Q.image Prod.snd) hqnotE hchain
  · -- hd_eq extends to P ∪ {t₂, J''}
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
  · -- reducedness bound: max hnb (J''+1)
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
  · -- r t₂ = q''
    simpa [q''] using repairSchedule_at_t d t₂ q'' (t₂ + 1 + j'')
  · -- r J'' = q''
    unfold r repairSchedule
    simp [q'']
  · -- r s = d s off {t₂, J''}
    intro s hs
    unfold r repairSchedule
    simp [show s ≠ t₂ by (intro h; exact hs (by simp [h])),
      show s ≠ t₂ + 1 + j'' by (intro h; exact hs (by simp [h]))]
  · -- caches agree up to t₂
    intro s hs
    exact schedCache_repairSchedule_eq_e d t₂ q'' (t₂ + 1 + j'') (by omega) σ C₀ hs

/-- Case A of the iteration (exchange step): at the first disagreement `t`, replace `d`'s
eviction `q = d t` with the policy's choice `q' = fifoSchedule σ C₀ t`, obtaining the new
schedule `e = exchangeSchedule d t q q' σ C₀`. Exact miss accounting: when the bad event
does not occur (`q'` is never requested again, or `d` faults at `J' = t + 1 + j'`), slack
increases by one (`exchangeSchedule_misses_le_plus_one`); otherwise slack is unchanged
(`exchangeSchedule_misses_le`); `e` agrees with FIF up to `t + 1` (`exchange_step'`). When
`q'` will be requested again (`hj'`), `e` is reduced from `J' + 1` on
(`exchangeSchedule_reduced_after`); when `q'` is never requested again, the reducedness
conclusion is vacuous (the condition is trivially true) — in that case the exchange is not
reduced at at most one branch-1 position (`d s = q'` faults), and its bound analysis is a
legacy blocker recorded in B5, left to `iterate_main` to assemble. -/
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
  · -- q' never requested again: agreement to t+1, slack +1 (if q is requested again) or unchanged (if q is also dead)
    have hagree' : agreeWithFIF e C₀ σ (t + 1) := by
      simpa [e, q, q'] using (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    by_cases hqnone : nextUse σ (t + 1) q = none
    · -- q also never requested again: misses not increased (the none branch of exchangeSchedule_misses_le), slack unchanged
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
    · -- q will be requested again: the bad event is impossible (q' dead), slack + 1
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
  · -- both q and q' will be requested again
    have hagree' : agreeWithFIF e C₀ σ (t + 1) := by
      simpa [e, q, q'] using (exchange_step' d σ C₀ hdred hC₀ ht hagree hdis).2
    have hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact getD_ne_nextUse (k := k) hj' (by omega) (by omega)
    by_cases hbad : σ.getD (t + 1 + j') 0 ∈ schedCache d C₀ σ (t + 1 + j')
    · -- the bad event occurs: slack unchanged
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
    · -- the bad event does not occur: slack + 1
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

/-- The exchange step of case one (`q'` never requested again): after one exchange, the new
schedule agrees with FIF up to `t + 1`; slack: +1 when `q` will be requested again
(`exchangeSchedule_misses_le_plus_one`), unchanged when `q` is also dead; reducedness: at
faults from `t + 1` on, the exchange evicts a resident page or `d s = q'` (branch 1 — the
exchange evicts `q'` as a no-op, not resident; this position occurs at most once). The hnone
branch of `iterate_main_exchange` gives the slack and agreement; the branch structure of
`exchangeDecision` (apart from branch 1: branches 3/5/6 evict pages of `E`, and the `else 0`
is excluded by faulting plus the cardinality argument) gives the reducedness. -/
lemma iterate_main_case_one (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hdred : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hnone : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none)
    (slack : ℕ) :
    ∃ slack',
      agreeWithFIF (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ (t + 1) ∧
      schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ + slack' ≤
        schedMisses d C₀ σ + slack ∧
      ∀ s, t + 1 ≤ s → σ.getD s 0 ∉ schedCache (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s →
        (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) s ∈
          schedCache (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s ∨
        d s = fifoSchedule σ C₀ t := by
  let q : Page := d t
  let q' : Page := fifoSchedule σ C₀ t
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  rcases iterate_main_exchange d σ C₀ hC₀ ht hagree hdis hdred slack with ⟨slack', hagreeE, hbookE, hredE⟩
  refine ⟨slack', ?_, ?_, ?_⟩
  · -- agreement up to t+1
    simpa [e, q, q'] using hagreeE
  · -- slack bookkeeping
    simpa [e, q, q'] using hbookE
  · -- reducedness (apart from branch 1)
    intro s hs hFault
    by_cases hd1 : d s = q'
    · right
      simpa [q'] using hd1
    · left
      have hFault' : σ.getD s 0 ∉ schedCache e C₀ σ s := by
        simpa [e, q, q'] using hFault
      have hmain : (exchangeScheduleCore d t q q' σ C₀ s).2 ∈ schedCache e C₀ σ s := by
        rw [exchangeScheduleCore_second]
        rw [← schedCache_exchangeScheduleCore]
        change exchangeDecision d t q q' σ C₀ (schedCache e C₀ σ s) s ∈ schedCache e C₀ σ s
        unfold exchangeDecision
        rw [if_neg (by omega)]
        rw [if_neg (by omega)]
        rw [if_neg hd1]
        by_cases hb3 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧ σ.getD s 0 ∈ schedCache d C₀ σ s
        · rw [if_pos hb3]
          let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
          by_cases hf : (M.filter (fun x => x ≠ q')).Nonempty
          · rw [dif_pos hf]
            exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Classical.choose_spec hf)).1).1
          · by_cases hm : M.Nonempty
            · rw [dif_neg hf]
              rw [dif_pos hm]
              exact (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
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
                exact exchangeScheduleCore_card d t q q' σ C₀ hdred (by omega)
              have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
                Finset.eq_of_subset_of_card_le hsub hcard
              exact hFault' (hEq ▸ hb3.2)
        · rw [if_neg hb3]
          by_cases hdsin : d s ∈ schedCache e C₀ σ s
          · rw [if_pos hdsin]
            exact hdsin
          · rw [if_neg hdsin]
            let M : Finset Page := schedCache e C₀ σ s \ schedCache d C₀ σ s
            by_cases hm : M.Nonempty
            · rw [dif_pos hm]
              exact (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
            · rw [dif_neg hm]
              exfalso
              have hsub : schedCache e C₀ σ s ⊆ schedCache d C₀ σ s := by
                intro y hy
                by_contra hyn
                exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
              have hcard : (schedCache d C₀ σ s).card ≤ (schedCache e C₀ σ s).card := by
                rw [show schedCache e C₀ σ s = (exchangeScheduleCore d t q q' σ C₀ s).1 by
                  rw [← schedCache_exchangeScheduleCore]]
                exact exchangeScheduleCore_card d t q q' σ C₀ hdred (by omega)
              have hEq : schedCache e C₀ σ s = schedCache d C₀ σ s :=
                Finset.eq_of_subset_of_card_le hsub hcard
              have hdFault : σ.getD s 0 ∉ schedCache d C₀ σ s := by
                intro h
                exact hFault' (hEq ▸ h)
              have hdsE : d s ∈ schedCache d C₀ σ s := hdred s (by omega) hdFault
              exact hdsin (hEq.symm ▸ hdsE)
      change (exchangeScheduleCore d t q q' σ C₀ s).2 ∈ schedCache e C₀ σ s
      exact hmain

/-- FIF's eviction page `p` at `t` (FIF faults and evicts at the disagreement) is absent
from FIF's own cache before the first request `J = t + 1 + j`: the base step follows from
the `hftF` fault plus `p`'s residence, and afterwards `nextUse` excludes requests while the
cache only admits requested pages. -/
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
      · -- base step: s+1 = t+1, the cache evicts p and the request σ[t] ≠ p
        subst s
        rw [schedCache]
        rw [if_neg hftF]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hpeq | hmem
        · exact hftF (hpeq ▸ hp_mem)
        · exact (Finset.mem_erase.mp hmem).1 hp
      · -- step: the request σ[s] ≠ p, and p ∉ F_s (induction), hence p ∉ F_{s+1}
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

/-- At a nop position `s` (the nop `s = tₗ + 1 + jₗ` of some pair `(tₗ, qₗ)`), the current
schedule `d`'s eviction is a no-op: `d s ∉ D_s`. `hcomp` gives `d s = qₗ`, and `qₗ` is FIF's
eviction page at `tₗ` (`hQfifo`), first requested at `s`
(`fifo_evict_absent_until_request` plus agreement with FIF up to `s`), hence `qₗ ∉ D_s`. -/
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
  · -- s is also some pair's repair position: contradicts hpast (tₗ < t0 < s = tₗ)
    rcases hc1 with ⟨tₗ, qₗ, htqₗ, hteqₗ, hdtₗ⟩
    have htₗt0 : tₗ < t0 := hpast tₗ qₗ htqₗ
    omega
  · -- nop position: d s = qₗ, while qₗ ∉ D_s (FIF evicts at tₗ, first requested at s)
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

/-- Sharpening hQ: at the first disagreement `t₂` (`t₂` is a B2 resident, `d t₂ ∈ D_{t₂}`),
the first request `J''ᵢ = tᵢ + 1 + j''ᵢ` of a past repair pair `(tᵢ, q''ᵢ)` is strictly
after `t₂`: when `J''ᵢ < t₂`, the request at `J''ᵢ` is a nop for d (evicting `q''ᵢ` is not
in the cache), while FIF's eviction page `f` at `J''ᵢ` belongs to `D_{J''ᵢ+1}` (d's nop only
adds `q''ᵢ`) but not to `F_{J''ᵢ+1}` (FIF swaps out `f`) — contradicting agreement at
`J''ᵢ + 1 ≤ t₂`; when `J''ᵢ = t₂`, `σ[t₂] = q''ᵢ` and `d t₂ ∉ D_{t₂}`
(`nop_position_noop`) — contradicting the B2 residency. Gives the strict form
`t₂ < J''ᵢ` needed by the B2 step. -/
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
    · -- J''ᵢ < t₂: cache disagreement at J''ᵢ + 1 ≤ t₂
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
    · -- J''ᵢ = t₂: σ[t₂] = q''ᵢ and d t₂ ∉ D_{t₂} (nop), contradicting hqin
      have hs_eq : tᵢ + 1 + j'' = t₂ := by omega
      have ht₀t₂' : t0 < t₂ := by omega
      have hnoop : d t₂ ∉ schedCache d C₀ σ t₂ := nop_position_noop σ C₀ hC₀ d (t₂ := t₂) hagree
        Q P t0 hpast hcomp hpair hQfifo (ht₀s := ht₀t₂') (hs := le_rfl)
        (hP_in t₂ (Or.inr ⟨tᵢ, q'', j'', htq, hnext, hs_eq.symm⟩))
      exact hnoop hqin

/- ### The q₀'-B1 slack supply (the q₀' half of bad ≤ slack)

Branch-1 converse: the exchange evicts `q'` at `s > t` iff the source `d` evicts `q'` at `s`
(branch 1 of `exchangeDecision`; the other branches evict pages of `E` or `d s`, and the
`else 0` is excluded by `q' ∉ E` together with faulting plus the cardinality argument). By
`b1_exchange_no_bad_q0`: a B1 position `t₂` in the window with `d t₂ = q₀'` (`t₂ ∉ P`, and
both the source and the exchange fault at `t₂`) is the first branch 1 of the window
(`window_branch1_once`), hence the source's eviction of `q₀'` is genuine
(`q₀' ∈ D₀_{t₂}` — the forward induction from `t₀+1`: no branch 1 means no eviction, and
requests `≠ q₀'`), and the induction of `evicted_page_absent_until_request` (the t₂ version,
using `hj'₀`'s bound directly) gives `q₀' ∉ D₀_{J'₀}` — the exchange's bad event did not
occur. `b1_bad_le_slack_q0` then gives `bad ≤ slack` (when the bad event occurs, `slack ≥ 1`). -/

/-- Branch-1 converse: the exchange evicting `q'` at `s > t` ⟹ the source `d` evicts `q'`
at `s`. The structure of `exchangeDecision`: branch 1 evicts `q'`; branches 4-6 evict pages
of `E − D` (contradicting `q' ∉ E`); the `else 0` is excluded by faulting plus the
cardinality argument. -/
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

/-- The q₀'-B1 slack supply: a B1 position `t₂` in the window with `d t₂ = q₀'`
(`t₂ ∉ P`, and both the source and the exchange fault at `t₂`) makes the exchange's bad
event not occur: `q₀' ∉ D₀_{J'₀}`. Via the branch-1 converse, `d t₂ = q₀'` gives the
source's `d_pre t₂ = q₀'`; `window_branch1_once` gives that `t₂` is the first branch 1 of
the window, hence the source's eviction of `q₀'` is genuine (forward induction: from `t₀+1`
on there is no eviction of `q₀'` and requests `≠ q₀'`), and then the t₂ version of
`evicted_page_absent_until_request` (using `hj'₀`'s bound directly) gives that `q₀'` is
absent on `(t₂, J'₀]`. -/
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
  -- 1. branch-1 converse: d_pre t₂ = q₀'
  have hq'notE : q₀' ∉ schedCache e C₀ σ t₂ := by
    dsimp [e]
    exact exchangeSchedule_q'_absent d_pre t₀ q₀ q₀' σ C₀ hweak hft₀ hq'res hj' ht₀t₂ (le_of_lt ht₂J)
  have hdpre : d_pre t₂ = q₀' := by
    exact exchangeSchedule_eq_q'_imp_d_eq_q' d_pre t₀ q₀ q₀' σ C₀ hweak ht₀t₂ hq'notE hFaultE
      ((hd_eq t₂ ht₂notP).symm.trans hd)
  -- 2. t₂ is the first branch 1 of the window: ∀ s ∈ (t₀, t₂), faulting ⟹ d_pre s ≠ q₀'
  have hfirst : ∀ s, t₀ < s → s < t₂ → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ≠ q₀' := by
    intro s hs1 hs2 hFaults
    intro hbs
    exact window_branch1_once d_pre t₀ q₀ q₀' σ C₀ hweak hq'res hj'
      hs1 (by omega) ht₀t₂ (by omega) (by omega) hbs hdpre hFaults hFault
  -- 3. genuine eviction: q₀' ∈ D₀_{t₂} (from t₀+1 on there is no eviction of q₀' and requests ≠ q₀')
  have hq'keep : q₀' ∈ schedCache d_pre C₀ σ t₂ := by
    have hmain : ∀ s, t₀ + 1 ≤ s → s ≤ t₂ → q₀' ∈ schedCache d_pre C₀ σ s := by
      intro s
      induction s with
      | zero => omega
      | succ s ih =>
          intro hs1 hs2
          by_cases hst : s = t₀
          · -- base step: s+1 = t₀+1, the source evicts q₀ (≠ q₀'), q₀' is kept
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
          · -- step: the request σ[s] ≠ q₀', and there is no eviction of q₀' at s (excluded by branch 1)
            have hs1' : t₀ + 1 ≤ s := by omega
            have hs2' : s ≤ t₂ := by omega
            have hqin : q₀' ∈ schedCache d_pre C₀ σ s := ih hs1' hs2'
            have hneq : σ.getD s 0 ≠ q₀' := getD_ne_nextUse (k := s) hj' (by omega) (by omega)
            by_cases hf : σ.getD s 0 ∈ schedCache d_pre C₀ σ s
            · -- hit: cache unchanged
              rw [schedCache]
              rw [if_pos hf]
              exact hqin
            · -- fault: d_pre s ≠ q₀' (hfirst), hence q₀' is kept
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
  -- 4. the t₂ version of evicted_page_absent_until_request: q₀' ∉ D₀_s on (t₂, J'₀]
  have habs : ∀ s, t₂ < s → s ≤ t₀ + 1 + j₀' → q₀' ∉ schedCache d_pre C₀ σ s := by
    intro s
    induction s with
    | zero => omega
    | succ s ih =>
        intro hs1 hs2
        by_cases hst : s = t₂
        · -- base step: s+1 = t₂+1, the cache evicts q₀' and the request σ[t₂] ≠ q₀'
          subst s
          rw [schedCache]
          rw [if_neg hFault]
          rw [hdpre]
          intro hm
          rcases Finset.mem_insert.mp hm with hqeq | hm
          · exact hFault (show σ.getD t₂ 0 ∈ schedCache d_pre C₀ σ t₂ from by rwa [← hqeq])
          · exact (Finset.mem_erase.mp hm).1 rfl
        · -- step: q₀' ∉ D_s (induction), and the request σ[s] ≠ q₀'
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
  -- 5. σ[J'₀] = q₀', hence the bad event (σ[J'₀] ∈ D₀_{J'₀}) does not occur
  intro hbad
  have hsig : σ.getD (t₀ + 1 + j₀') 0 = q₀' := getD_eq_nextUse hj'
  exact habs (t₀ + 1 + j₀') (by omega) le_rfl (hsig ▸ hbad)

/-- The q₀'-B1 slack invariant: `bad ≤ slack`. When the bad event (`σ[J'''] ∈ D_{J'''}`)
occurs, `bad = 1`, and `hslack` (`1 ≤ slack` — when the exchange's bad event does not occur,
`exchange_step_slack` gives `slack' = slack + 1`, and the q₀'-B1 is the first step of the
window, so there is no intermediate consumption) gives `bad ≤ slack`. -/
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

/-- The absence of `q''` in the dead-page repair `r = repairSchedule e t q'' t`: `q''` is
evicted at `t` and never requested again, hence `q'' ∉ Ŝ_s` for all `t < s < σ.length`. -/
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
      · -- base step: s+1 = t+1
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
      · -- step: the request σ[s] ≠ q'', and q'' ∉ S_s (induction), hence q'' ∉ S_{s+1}
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

/-- Dead-page absence (version for s ≥ σ.length): when `q'' ≠ 0`, `σ.getD s 0 = 0 ≠ q''`,
so requests avoid `q''` and the absence holds for all `s > t`. -/
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
        · -- base step: s+1 = t+1
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
        · -- step: the request σ[s] ≠ q'' (use nextUse for s < σ.length; when s ≥ σ.length, σ[s] = 0 ≠ q''),
          -- and q'' ∉ S_s (induction), hence q'' ∉ S_{s+1}
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

/-- The dead-page version of case B1: at a no-op disagreement `t₂` where
`q'' = fifoSchedule σ C₀ t₂` is never requested again (`hq''dead`), the dead-page repair
`r = repairSchedule d t₂ q'' t₂` (nop = `t₂`) satisfies: agreement up to `t₂ + 1`
(`repair_step_qp_dead`), misses not increased (free, no bad event), the chain extends to
`insert q'' (Q.image Prod.snd)` (`E − Ŝ ⊆ {q''}` from `repair_diff_noop_qp_dead`),
`hd_eq` extends to `P ∪ {t₂}`, and the reducedness bound `hnb` is preserved. -/
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
      (∀ s, hnb ≤ s → s < σ.length → σ.getD s 0 ∉ schedCache r C₀ σ s → r s ∈ schedCache r C₀ σ s) ∧
      r t₂ = fifoSchedule σ C₀ t₂ ∧
      (∀ s, s ∉ ({t₂} : Finset ℕ) → r s = d s) ∧
      (∀ s, s ≤ t₂ → schedCache r C₀ σ s = schedCache d C₀ σ s) := by
  let q'' : Page := fifoSchedule σ C₀ t₂
  let r : ℕ → Page := repairSchedule d t₂ q'' t₂
  have hstep := repair_step_qp_dead d σ C₀ hC₀ ht₂ hagree hdis hnoop hq''dead
  refine ⟨r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- agreement up to t₂+1
    exact hstep.2
  · -- misses not increased (free)
    exact hstep.1
  · -- chain: E − Ŝ ⊆ insert q'' (Q.image)
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
  · -- hd_eq extends to P ∪ {t₂}
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
  · -- reducedness bound hnb preserved: r = d off {t₂}, q'' resident at t₂
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
    · -- s ≠ t₂: r s = d s; D − Ŝ ⊆ {q''}, hence d s ∈ Ŝ_s unless d s = q''
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
      · -- d s = q'': contradicts hdnoevict (the current schedule never evicts q'')
        exfalso
        exact hdnoevict s hs (hdsq.trans (by dsimp [q'']))
      · -- d s ≠ q'': by contradiction, d s ∉ Ŝ_s would give d s ∈ D − Ŝ ⊆ {q''}, a contradiction
        by_contra hnotS
        have hmem : d s ∈ schedCache d C₀ σ s \ schedCache r C₀ σ s := by
          rw [Finset.mem_sdiff]
          exact ⟨hred, hnotS⟩
        exact hdsq (Finset.mem_singleton.mp (hdiff.1 hmem))
  · -- r t₂ = q''
    simpa [q''] using repairSchedule_at_t d t₂ q'' t₂
  · -- r s = d s off {t₂}
    intro s hs
    unfold r repairSchedule
    simp [show s ≠ t₂ by (intro h; exact hs (by simp [h]))]
  · -- caches agree up to t₂
    intro s hs
    exact schedCache_repairSchedule_eq_e_qp_dead d t₂ q'' σ C₀ hs
/-- The exchange schedule of the current window: when `win = none` (no exchange yet), take
the fallback schedule `fb` (the chain/eviction-agreement invariants are then trivial); when
`win = some (d_pre, t₀, q₀, q₀', j₀, j₀')`, take the exchange schedule of that window. -/
noncomputable def windowExchange (win : Option ((ℕ → Page) × ℕ × Page × Page × ℕ × ℕ))
    (fb : ℕ → Page) (σ : List Page) (C₀ : Finset Page) : ℕ → Page :=
  match win with
  | none => fb
  | some w => exchangeSchedule w.1 w.2.1 w.2.2.1 w.2.2.2.1 σ C₀

/-- IterateState: state (d, t0, slack, hnb, Q, P) plus window, invariants per DESIGN. -/
structure IterateState (σ : List Page) (C₀ : Finset Page) (M : ℕ) where
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
      · -- case B: t < hnb, split into B2/B1 according to whether d t is resident
        by_cases hqin : st.d t ∈ schedCache st.d C₀ σ t
        · -- B2: no_nop_at_b2 gives t ∉ P
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
        · -- B1: no-op repair
          rcases hB1 st t htl hB hagt hdis hqin hft₂ with ⟨st', ht0'⟩
          have hmea : σ.length - st'.t0 < n := by
            rw [ht0']
            omega
          rcases ih (σ.length - st'.t0) hmea st' rfl with ⟨d', slack', hagree', hbook'⟩
          exact ⟨d', slack', hagree', hbook'⟩
      · -- case A: hnb ≤ t, exchange; if q' is alive the window resets, if q' is dead it is supplied by hAone
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

  /-- Legacy conditional candidate for CLRS Theorem 15.5 via `iterate_main` from
  the initial state.  This is deliberately not named `fifo_optimal`: the public
  theorem is unconditional, while this archived route still assumes the
  `hB1`/`hB2`/`hAone` supplies. -/
  private lemma fifo_optimal_conditional_legacy
      (π : Policy) (C₀ : Finset Page) (σ : List Page)
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
