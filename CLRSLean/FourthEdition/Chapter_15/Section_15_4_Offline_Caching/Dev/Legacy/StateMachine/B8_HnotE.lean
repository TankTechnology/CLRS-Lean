import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.Legacy.StateMachine.B7_Iteration

/-!
# Dev B8: the hnotE derivation (Q''-exclusion at window faults)

Development file for the `hnotE` premise of the current-schedule keep-swap
(`repair_keep_swap_cur` and its q''-dead sibling, B7): at a B2 position
`t₂`, for `s ∈ (t₂, J]` with `s ∉ P` and `σ[s] ∉ D_s`, prove `σ[s] ∉ E_s`
(the exchange schedule never hits where the current schedule faults, off the
past repair positions).

**Corrected mechanism** (2026-08-11, `Dev/search_hnot.py` — the DESIGN's
"`q''ᵢ` requested at `nᵢ ≤ s`, kept" mechanism is *empirically false*:
172 of 180 later requests of a pair page have `q''ᵢ ∉ D_s`, because the
current schedule re-evicts it — e.g. `σ = [1,1,3,4,1,3,2,3]`, B2 at 6,
`d 6 = 3 = q''ᵢ` a real eviction).  The correct invariant (0 violations
over σ of length 4-9, alphabet 1..4, min-resident d₀):

- `pair_q''_absent_d`: after the repair at `tᵢ` evicts `q''ᵢ`, the page
  stays out of the current cache until its first request `nᵢ`
  (`q''ᵢ ∉ D_s` on `(tᵢ, nᵢ]` — clean induction, request-avoidance only).
  This makes the nop `nᵢ` a no-op and keeps `q''ᵢ ≠ q''ₖ` at other pairs'
  nops.
- `pair_page_in_D_of_in_E`: the joint E⟹D induction — for every alive
  past pair with `nᵢ < s`, `q''ᵢ ∈ E_s ⟹ q''ᵢ ∈ D_s` (window positions,
  `hnot` excludes `P`).  The step's only obstacle is the e-hit-at-d-fault
  at `s` (`σ[s] ∈ E_s − D_s`): the chain pushes `σ[s]` into `Q.image`, and
  the pair analysis (dead / before-`nₗ` / at-`nₗ`-in-P / after-`nₗ`-via-the
  IH) contradicts it.  At an e-fault with `q'' = σ[s]` (the request at `s`)
  the conclusion is direct (both caches gain `σ[s]`).
- `b2_hnotE`: the assembly — `σ[s] ∈ E_s` pushes `σ[s]` into
  `Q.image` (chain), then dead / `s < nᵢ` (first request) / `s = nᵢ`
  (`hP_in`) / `s > nᵢ` (`pair_page_in_D_of_in_E` — the request `σ[s] = q''ᵢ`
  is then in `D_s`, contradicting the d-fault).

Main results:

- `pair_q''_absent_d`: `q''` stays out of the current cache on `(tᵢ, nᵢ]`
- `pair_page_in_D_of_in_E`: the E⟹D membership for alive pair pages
- `b2_hnotE`: the `hnotE` premise — the Q''-exclusion at window faults

This file is part of the `fifo_optimal` iteration; it will be merged into
`S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

set_option maxHeartbeats 400000

/-- After the repair at `tᵢ` evicts `q''`, the page `q''` does not return to the
cache of the current schedule `d` before the first request `nᵢ = tᵢ + 1 + j''`:
`d tᵢ = q''` (a genuine eviction, `q'' ∈ D_{tᵢ}`), and thereafter requests
avoid `q''` (the first request is at `nᵢ`), so the cache only admits requested
pages. This yields the no-op property at the nop positions (`q'' ∉ D_{nᵢ}`) and
page distinctness across pairs (`q''ₖ ≠ q''ᵢ`, given at other pairs' nops by
this lemma plus the E⟹D membership). -/
lemma pair_q''_absent_d (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {tᵢ : ℕ} {q'' : Page} (hftᵢ : σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ)
    (hq''in : q'' ∈ schedCache d C₀ σ tᵢ) (hd : d tᵢ = q'')
    {j'' : ℕ} (hj'' : nextUse σ (tᵢ + 1) q'' = some j'') :
    ∀ s, tᵢ < s → s ≤ tᵢ + 1 + j'' → q'' ∉ schedCache d C₀ σ s := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs1 hs2
      by_cases hs_eq : s = tᵢ
      · -- base step: s+1 = tᵢ+1, the cache evicts q'' and the request σ[tᵢ] ≠ q''
        subst s
        rw [schedCache]
        rw [if_neg hftᵢ]
        intro hmem
        rcases Finset.mem_insert.mp hmem with hpeq | hmem
        · exact hftᵢ (hpeq ▸ hq''in)
        · exact (Finset.mem_erase.mp hmem).1 hd.symm
      · -- step: the request σ[s] ≠ q'', and q'' ∉ D_s (induction), so q'' ∉ D_{s+1}
        have hst : tᵢ < s := by omega
        have hih : q'' ∉ schedCache d C₀ σ s := ih (by omega) (by omega)
        have hneq : σ.getD s 0 ≠ q'' := getD_ne_nextUse (k := s) hj'' (by omega) (by omega)
        rw [schedCache]
        by_cases hhit : σ.getD s 0 ∈ schedCache d C₀ σ s
        · rw [if_pos hhit]
          exact hih
        · rw [if_neg hhit]
          intro hmem
          rcases Finset.mem_insert.mp hmem with hpeq | hmem
          · exact hneq hpeq.symm
          · exact hih (Finset.mem_erase.mp hmem).2

/-- E⟹D for alive pair pages (joint induction): within the B2 window `(t₂, J]`,
at a position `s`, any alive pair `(tᵢ, q'')` with `nᵢ < s` satisfies
`q'' ∈ E_s ⟹ q'' ∈ D_s`.  The inductive step (the update at position `s`):
- at an e hit, `q'' ∈ E_s` (the cache is unchanged); the d-fault case
  (`σ[s] ∈ E_s − D_s`) is excluded by the chain plus the pair's own induction
  hypothesis (the e-hit-at-d-fault contradiction);
- at an e fault, `q'' ∈ E(s+1)` is obtained from `q'' = σ[s]` (a request, both
  sides gain `q''`) or from `q'' ∈ E_s ∧ e s ≠ q''`; the latter uses `hd_eq`
  at `s ∉ P` (`d s = e s ≠ q''`).
- the base case of a new pair (`nᵢ = s`, first request): the request
  `σ[s] = q''` makes `q''` enter `D(s+1)`. -/
lemma pair_page_in_D_of_in_E (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hagree : agreeWithFIF d C₀ σ t₂)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (d t₂) = some j)
    (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (hchain : ∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
        schedCache d C₀ σ s ⊆ Q.image Prod.snd)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'')
    (hQfifo : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = fifoSchedule σ C₀ tᵢ)
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q''))
    (hpair : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = some j'' →
      σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧ q'' ∈ schedCache d C₀ σ tᵢ ∧ d tᵢ = q'')
    (hP_in : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ P)
    {s : ℕ} (ht₂s : t₂ < s) (hsJ : s ≤ t₂ + 1 + j)
    {tᵢ : ℕ} {q'' : Page} (htq : (tᵢ, q'') ∈ Q)
    {j'' : ℕ} (hnext : nextUse σ (tᵢ + 1) q'' = some j'')
    (hsn : tᵢ + 1 + j'' < s) :
    q'' ∈ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s →
      q'' ∈ schedCache d C₀ σ s := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  let E : ℕ → Finset Page := schedCache e C₀ σ
  let D : ℕ → Finset Page := schedCache d C₀ σ
  have hJlen : t₂ + 1 + j < σ.length := by
    have hjlt : j < (σ.drop (t₂ + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt
    omega
  have hmain : ∀ s : ℕ, t₂ < s → s ≤ t₂ + 1 + j →
      (∀ (t' : ℕ) (q' : Page) (j' : ℕ), (t', q') ∈ Q →
        nextUse σ (t' + 1) q' = some j' →
        t' + 1 + j' < s → q' ∈ E s → q' ∈ D s) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro hs1 hs2
        intro t' q' j' htq' hnext' hsn'
        have ht₂n : t₂ < t' + 1 + j' := by
          rcases hQ t' q' htq' with hdead | ⟨j₀, hnext₀, ht₂J₀⟩
          · exfalso
            rw [hnext'] at hdead
            cases hdead
          · have hj : j₀ = j' := Option.some.inj (hnext₀.symm.trans hnext')
            omega
        by_cases hne : t' + 1 + j' = s - 1
        · -- new pair: nᵢ = s−1, the first request σ[s−1] = q', so q' enters D s
          have hsig : σ.getD (s - 1) 0 = q' := by
            rw [← hne]
            exact getD_eq_nextUse hnext'
          intro hE'
          dsimp [D]
          rw [show s = (s - 1) + 1 by omega, schedCache]
          by_cases hhit : σ.getD (s - 1) 0 ∈ schedCache d C₀ σ (s - 1)
          · rw [if_pos hhit]
            exact hsig ▸ hhit
          · rw [if_neg hhit]
            rw [hsig]
            exact Finset.mem_insert_self _ _
        · -- old pair: nᵢ < s−1, inductive step
          have hsnlt : t' + 1 + j' < s - 1 := by omega
          intro hE'
          by_cases he : σ.getD (s - 1) 0 ∈ E (s - 1)
          · -- e hits at s−1: E s = E (s−1), hence q' ∈ E (s−1)
            have hEsucc : E s = E (s - 1) := by
              dsimp [E]
              conv => lhs; rw [show s = (s - 1) + 1 by omega]
              rw [schedCache]
              rw [if_pos he]
            have hqE : q' ∈ E (s - 1) := by
              simpa [hEsucc] using hE'
            have hqD : q' ∈ D (s - 1) :=
              ih (s - 1) (by omega) (by omega) (by omega) t' q' j' htq' hnext' hsnlt hqE
            by_cases hd' : σ.getD (s - 1) 0 ∈ D (s - 1)
            · -- d hits: D s = D (s−1)
              dsimp [D]
              rw [show s = (s - 1) + 1 by omega, schedCache]
              rw [if_pos hd']
              exact hqD
            · -- d faults while e hits: e-hit-at-d-fault, the chain plus induction contradiction
              exfalso
              have hq : σ.getD (s - 1) 0 ∈ Q.image Prod.snd :=
                b2_ehit e d σ C₀ hd' (Q.image Prod.snd) (hchain (s - 1) (by omega)) he
              rcases Finset.mem_image.mp hq with ⟨⟨tₗ, q''ₗ⟩, htqₗ, hsigq⟩
              have htₗlt : tₗ < t₂ := hpast tₗ q''ₗ htqₗ
              rcases hQ tₗ q''ₗ htqₗ with hdead | ⟨jₗ, hnextₗ, ht₂Jₗ⟩
              · exact getD_ne_of_nextUse_none σ hdead (by omega) (by omega) hsigq.symm
              · by_cases hslt : s - 1 < tₗ + 1 + jₗ
                · exact getD_ne_nextUse (k := s - 1) hnextₗ (by omega) hslt hsigq.symm
                · by_cases hseq : s - 1 = tₗ + 1 + jₗ
                  · exfalso
                    have hsP : s - 1 ∈ P :=
                      hP_in (s - 1) (Or.inr ⟨tₗ, q''ₗ, jₗ, htqₗ, hnextₗ, hseq⟩)
                    exact (hnot (s - 1) (by omega) (by omega)) hsP
                  · have hsgt : tₗ + 1 + jₗ < s - 1 := by omega
                    have hsigq' : q''ₗ = σ.getD (s - 1) 0 := by simpa using hsigq
                    have hqEₗ : q''ₗ ∈ E (s - 1) := by
                      rw [hsigq']
                      exact he
                    have hqDₗ : q''ₗ ∈ D (s - 1) :=
                      ih (s - 1) (by omega) (by omega) (by omega) tₗ q''ₗ jₗ htqₗ hnextₗ
                        hsgt hqEₗ
                    exact hd' (hsigq.symm ▸ hqDₗ)
          · -- e faults at s−1: E s = insert σ[s−1] (E (s−1) − e (s−1))
            have hEsucc : E s = insert (σ.getD (s - 1) 0) ((E (s - 1)).erase (e (s - 1))) := by
              dsimp [E]
              rw [show s = (s - 1) + 1 by omega, schedCache]
              rw [if_neg he]
              rfl
            have hmem : q' ∈ insert (σ.getD (s - 1) 0) ((E (s - 1)).erase (e (s - 1))) := by
              rwa [← hEsucc]
            rcases Finset.mem_insert.mp hmem with hqeq | hqin
            · -- q' = σ[s−1]: a request, both sides gain q'
              dsimp [D]
              rw [show s = (s - 1) + 1 by omega, schedCache]
              by_cases hd' : σ.getD (s - 1) 0 ∈ D (s - 1)
              · rw [if_pos hd']
                exact hqeq.symm ▸ hd'
              · rw [if_neg hd']
                rw [hqeq]
                exact Finset.mem_insert_self _ _
            · -- q' ∈ E (s−1) ∧ e (s−1) ≠ q'
              have hqE : q' ∈ E (s - 1) := (Finset.mem_erase.mp hqin).2
              have hqD : q' ∈ D (s - 1) :=
                ih (s - 1) (by omega) (by omega) (by omega) t' q' j' htq' hnext' hsnlt hqE
              have hsnotP : s - 1 ∉ P := hnot (s - 1) (by omega) (by omega)
              have hds : d (s - 1) = e (s - 1) := hd_eq (s - 1) hsnotP
              have hne' : e (s - 1) ≠ q' := by
                intro h
                exact (Finset.mem_erase.mp hqin).1 h.symm
              by_cases hd' : σ.getD (s - 1) 0 ∈ D (s - 1)
              · -- d hits: D s = D (s−1)
                dsimp [D]
                rw [show s = (s - 1) + 1 by omega, schedCache]
                rw [if_pos hd']
                exact hqD
              · -- d faults (e also faults): D s = insert σ[s−1] (D (s−1) − d (s−1)), d (s−1) ≠ q'
                dsimp [D]
                rw [show s = (s - 1) + 1 by omega, schedCache]
                rw [if_neg hd']
                rw [Finset.mem_insert]
                right
                rw [Finset.mem_erase]
                constructor
                · intro hq
                  exact hne' (hds.symm.trans hq.symm)
                · exact hqD
  exact hmain s ht₂s hsJ tᵢ q'' j'' htq hnext hsn

/-- The `hnotE` premise (Q'' exclusion): within the window `(t₂, J]` of the B2
position `t₂`, if `s ∉ P` and `d` faults at `s`, then the exchange schedule `e`
also faults at `s`: `σ[s] ∉ E_s`.  Derivation: `σ[s] ∈ E_s` pushes `σ[s]` into
`Q.image` via the chain, yielding `σ[s] = q''ᵢ` (some past repair pair);
a dead page and `s < nᵢ` (before the first request) contradict, `s = nᵢ` is a
nop position (in `P`, contradicting `s ∉ P`), and for `s > nᵢ`
`pair_page_in_D_of_in_E` gives `q''ᵢ ∈ D_s`, contradicting the d-fault. -/
lemma b2_hnotE (d_pre d : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    (hagree : agreeWithFIF d C₀ σ t₂)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (d t₂) = some j)
    (Q : Finset (ℕ × Page)) (P : Finset ℕ)
    (hchain : ∀ s, s ≤ σ.length → schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s \
        schedCache d C₀ σ s ⊆ Q.image Prod.snd)
    (hpast : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → tᵢ < t₂)
    (hQ : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'')
    (hQfifo : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q → q'' = fifoSchedule σ C₀ tᵢ)
    (hcomp : ∀ s, s ∈ P → (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ ∧ d s = q'') ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'' ∧ d s = q''))
    (hpair : ∀ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q →
      nextUse σ (tᵢ + 1) q'' = some j'' →
      σ.getD tᵢ 0 ∉ schedCache d C₀ σ tᵢ ∧ q'' ∈ schedCache d C₀ σ tᵢ ∧ d tᵢ = q'')
    (hP_in : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ Q ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ P)
    (hd_eq : ∀ s, s ∉ P → d s = (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) s)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ P)
    {s : ℕ} (ht₂s : t₂ < s) (hsJ : s ≤ t₂ + 1 + j) (hsnotP : s ∉ P)
    (hftd : σ.getD s 0 ∉ schedCache d C₀ σ s) :
    σ.getD s 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s := by
  let e : ℕ → Page := exchangeSchedule d_pre t₀ q₀ q₀' σ C₀
  have hJlen : t₂ + 1 + j < σ.length := by
    have hjlt : j < (σ.drop (t₂ + 1)).length := (nextUse_eq_some_iff.mp hj).1
    rw [List.length_drop] at hjlt
    omega
  intro he
  have hq : σ.getD s 0 ∈ Q.image Prod.snd :=
    b2_ehit e d σ C₀ hftd (Q.image Prod.snd) (hchain s (by omega)) he
  rcases Finset.mem_image.mp hq with ⟨⟨tᵢ, q''⟩, htq, hsigq⟩
  have htᵢlt : tᵢ < t₂ := hpast tᵢ q'' htq
  rcases hQ tᵢ q'' htq with hdead | ⟨j'', hnext, ht₂J⟩
  · exact getD_ne_of_nextUse_none σ hdead (by omega) (by omega) hsigq.symm
  · by_cases hslt : s < tᵢ + 1 + j''
    · exact getD_ne_nextUse (k := s) hnext (by omega) hslt hsigq.symm
    · by_cases hseq : s = tᵢ + 1 + j''
      · exfalso
        have hsP : s ∈ P := hP_in s (Or.inr ⟨tᵢ, q'', j'', htq, hnext, hseq⟩)
        exact hsnotP hsP
      · have hsgt : tᵢ + 1 + j'' < s := by omega
        have hsigq' : q'' = σ.getD s 0 := by simpa using hsigq
        have hqE : q'' ∈ schedCache e C₀ σ s := by
          rw [hsigq']
          exact he
        have hqD : q'' ∈ schedCache d C₀ σ s :=
          pair_page_in_D_of_in_E d_pre d t₀ q₀ q₀' σ C₀ hC₀ hagree ht₂ hj Q P hchain
            hpast hQ hQfifo hcomp hpair hP_in hd_eq hnot (s := s) ht₂s hsJ htq hnext hsgt hqE
        exact hftd (hsigq.symm ▸ hqD)

end Caching

end CLRS
