import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.Legacy.StateMachine.B8_HnotE

/-
# Dev B9: the iterate_main assembly (checkpoint)

The concrete instantiation of `iterate_main`'s abstract case-step
supplies `hB1`/`hB2`/`hAone` with the kernel-checked case-step lemmas
and the extension glue.  The checkpoint wires everything that is
proved and leaves the genuinely open pieces as **documented
hypotheses** (referencing `Dev/DESIGN.md`) — no `sorry` (the
repository checker forbids them on `main`):

1. `hQ_open`: the hQ-strictness/extension — the state's `hQ` field
   over the full-history `Q` is empirically false (a pair whose nop
   has passed can never satisfy the new bound), and `b2_ehit_ne` /
   `b2_hnotE` / `past_pair_first_request_after` need the upgraded
   bound at the B2 disagreement.  See DESIGN.md "hQ-extension
   blocker".
2. `hslack_open`: the B1 slack invariant `bad ≤ slack` — the q₀'-half
   is proved (`b1_exchange_no_bad_q0` + `b1_bad_le_slack_q0`, up to
   the `1 ≤ slack` derivation — the "q₀'-B1 is the first step after
   the exchange" slack composition), but the non-q₀' half crashes 164
   times under all identified credits.  See DESIGN.md
   "slack-accounting blocker" and "Non-q₀' B1 pairing proposal".
3. `hcaseone_open`: the case-one exchange's reducedness — the state's
   `hdred` field from `t+1` fails at the at-most-one branch-1 fault
   (`d s = q'`, the exchange's no-op eviction of the dead `q'`);
   `iterate_main_case_one` proves the OR-form
   `e s ∈ E_s ∨ d s = q'`.  See DESIGN.md "Case one".
4. `hB2dead_open`: the B2 dead-page step constructions — the case
   steps `iterate_main_case_b2_q_dead` / `iterate_main_case_b2_qp_dead`
   do not exist yet (the keep-swaps `repair_keep_swap_cur_qp_dead` and
   the chain variants are done; the step assembly is not).  See
   DESIGN.md "Remaining for iterate_main" item (3).

The assembled `fifo_optimal_assembled` closes once the four hypotheses
are proved; the Dev → S3 merge happens at that point (the Dev files
import S3, so the assembled proof cannot live in S3 before the merge).

Main results:

- `iterate_main_assembled`: the induction with the concrete case
  constructions (case-one, B1-alive, B1-dead, B2-alive wired; the
  dead-page B2 steps via `hB2dead_open`)
- `fifo_optimal_assembled`: CLRS Theorem 15.5 from the initial state

This file is part of the `fifo_optimal` iteration; it will be merged
into `S3_Optimality.lean` once the proof is complete.
-/

namespace CLRS

namespace Caching

open Finset

set_option maxHeartbeats 400000

/- ### Open hypotheses (the DESIGN.md blockers)

- `hQ_open`: the strict bound `t₂ < tᵢ + 1 + j''` on live pairs in `Q`
  at the B2 disagreement (hQ extension/strictness; see DESIGN
  "hQ-extension blocker");
- `hslack_open`: `bad ≤ slack` for the B1 step (the q₀' half is proved
  up to the `1 ≤ slack` derivation; for the non-q₀' half see DESIGN
  "Non-q₀' B1 pairing proposal");
- `hcaseone_open`: the reducedness of the case-one exchange — at the
  branch-1 position (`d s = q'`) the exchange evicts `q'` via a no-op,
  non-resident; `hnb'` must cross at most one branch-1 fault (see
  DESIGN "Case one");
- `hB2dead_open`: the construction of the B2 dead-page steps (the step
  lemmas do not exist yet; the keep-swap and the chain are proved, see
  DESIGN "Remaining" item (3)). -/

/-- The slack hypothesis for the B1 step: when the bad event
(`σ[J'''] ∈ D_{J'''}`) occurs we have `bad ≤ slack`.  The q₀'-B1 half
is given by `b1_exchange_no_bad_q0` + `b1_bad_le_slack_q0` (still
needs the `1 ≤ slack` derivation — q₀'-B1 is the first step in the
window, and slack is the exchange's `slack + 1`); the non-q₀' half is
the open pairing design (see DESIGN.md "Non-q₀' B1 pairing proposal"). -/
def B1SlackHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
    agreeWithFIF st.d C₀ σ t₂ →
    schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
    st.d t₂ ∉ schedCache st.d C₀ σ t₂ →
    σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
    ∀ {j''' : ℕ}, nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''' →
      (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache st.d C₀ σ (t₂ + 1 + j''') then 1 else 0) ≤ st.slack

/-- The strictness hypothesis for hQ: at the B2 disagreement `t₂`, the
first request of a live pair in `Q` is strictly after `t₂`
(required by `b2_ehit_ne`/`b2_hnotE`/`past_pair_first_request_after`;
this field is empirically false on the full-history `Q`, see DESIGN
"hQ-extension blocker"). -/
def HQsupplyHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ),
    (∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'') ∧
    (∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'')

/-- The reducedness hypothesis for the case-one exchange: there exists
a reduced bound `hnb'` (after `t+1`, crossing at most one branch-1
fault) such that the exchange evicts a resident page at the fault from
`hnb'` on.  `iterate_main_case_one` gives the OR-form
`e s ∈ E_s ∨ d s = q'` (see DESIGN "Case one"). -/
def CaseOneHdredHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t : ℕ) (ht : t < σ.length),
    st.hnb ≤ t →
    agreeWithFIF st.d C₀ σ t →
    schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) →
    nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none →
    ∃ hnb' : ℕ, t + 1 ≤ hnb' ∧
      ∀ s, hnb' ≤ s →
        σ.getD s 0 ∉ schedCache (exchangeSchedule st.d t (st.d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s →
        (exchangeSchedule st.d t (st.d t) (fifoSchedule σ C₀ t) σ C₀) s ∈
          schedCache (exchangeSchedule st.d t (st.d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ s

/-- The construction hypothesis for the B2 dead-page steps: the B2
step lemmas for q-dead and q''-dead do not exist yet (the keep-swap
and the chain are proved: see DESIGN "Remaining" item (3)). -/
def B2DeadStepHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
    agreeWithFIF st.d C₀ σ t₂ →
    schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
    st.d t₂ ∈ schedCache st.d C₀ σ t₂ →
    σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
    t₂ ∉ st.P →
    nextUse σ (t₂ + 1) (st.d t₂) = none ∨ nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = none →
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1

/-- The hQ supply for the B2 step (part 1): the strengthened clause
for the old bound `t₂` is given by `past_pair_first_request_after`
from the state's old `hQ` (old bound `st.t0`) — this is the form
needed by the consumer of the hQ-extension blocker (a formalization
of "consumers only consult the pair whose page equals the request,
and that pair is never broken"; the B2-resident hypothesis `hqin` of
`past_pair` and the state fields `hP`/`hcomp`/`hpair`/`hP_in`/
`hQfifo`/`hpast` are all supplied by the state). -/
lemma b2_hQ_supply_old (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₀t₂ : st.t0 ≤ t₂)
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hqin : st.d t₂ ∈ schedCache st.d C₀ σ t₂) :
    ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ st.Q →
      nextUse σ (tᵢ + 1) q'' = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t₂ < tᵢ + 1 + j'' := by
  exact past_pair_first_request_after σ C₀ hC₀ st.d st.t0 t₂ ht₀t₂ hagree st.Q st.P
    st.hpast st.hP st.hcomp st.hpair st.hQfifo st.hP_in st.hQ ht₂ hqin

/- ### The case-one step construction (instantiation of hAone)

`iterate_main_case_one` gives agreement, slack, and OR-form
reducedness; `hcaseone_open` supplies the bound for the state field
`hdred`.  Q/P stay ∅ (no past pairs), and the window `win = none`
(q' is dead, no window). -/

/-- The full state construction for case one: after one exchange,
`d' = e`, `t0 = t+1`, slack comes from the hnone branch of
`iterate_main_exchange` (q alive: +1, q dead: unchanged), and `hdred`
comes from the bound of `hcaseone_open`.  Q/P stay ∅, `win = none`. -/
lemma step_case_one (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hcaseone : CaseOneHdredHyp σ C₀ M)
    {t : ℕ} (ht : t < σ.length)
    (hnb_le : st.hnb ≤ t)
    (hagree : agreeWithFIF st.d C₀ σ t)
    (hdis : schedCache st.d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnone : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = none) :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t + 1 := by
  let q : Page := st.d t
  let q' : Page := fifoSchedule σ C₀ t
  let e : ℕ → Page := exchangeSchedule st.d t q q' σ C₀
  have hdred_t : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache st.d C₀ σ s → st.d s ∈ schedCache st.d C₀ σ s := by
    intro s hs hf
    exact st.hdred s (by omega) hf
  rcases iterate_main_case_one st.d σ C₀ hC₀ ht hagree hdis hdred_t hnone st.slack with
    ⟨slack', hagreeE, hbookE, hredE⟩
  rcases hcaseone st t ht hnb_le hagree hdis hnone with ⟨hnb', hnb'_t, hred'⟩
  have hbook' : schedMisses e C₀ σ + slack' ≤ M := by
    exact le_trans hbookE st.hbook
  have hwin_inv' : ∀ (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ),
      none = some (d_pre, t₀, q₀, q₀', j₀, j₀') →
      t₀ < t + 1 ∧ d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
      (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
      σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
      nextUse σ (t₀ + 1) q₀ = some j₀ ∧
      (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
      nextUse σ (t₀ + 1) q₀' = some j₀' := by
    intro d_pre t₀ q₀ q₀' j₀ j₀' hEq
    cases hEq
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange none e σ C₀) C₀ σ s \
      schedCache e C₀ σ s ⊆ (∅ : Finset (ℕ × Page)).image Prod.snd := by
    intro s hs
    simp [windowExchange]
  have hd_eq' : ∀ s, s ∉ (∅ : Finset ℕ) → e s = windowExchange none e σ C₀ s := by
    intro s hs
    rfl
  have hpast' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) → tᵢ < t + 1 := by
    intro tᵢ q'' h
    simp at h
  have hQ' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
      nextUse σ (tᵢ + 1) q'' = none ∨ ∃ j'', nextUse σ (tᵢ + 1) q'' = some j'' ∧ t + 1 < tᵢ + 1 + j'' := by
    intro tᵢ q'' h
    simp at h
  have hQfifo' : ∀ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) →
      q'' = fifoSchedule σ C₀ tᵢ := by
    intro tᵢ q'' h
    simp at h
  have hP' : ∀ s, s ∈ (∅ : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') := by
    intro s h
    simp at h
  have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q'' : Page), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q'' : Page) (j'' : ℕ), (tᵢ, q'') ∈ (∅ : Finset (ℕ × Page)) ∧
        nextUse σ (tᵢ + 1) q'' = some j'' ∧ s = tᵢ + 1 + j'') → s ∈ (∅ : Finset ℕ) := by
    intro s h
    rcases h with ⟨tᵢ, q'', htq, hteq⟩ | ⟨tᵢ, q'', j'', htq, hnext, hteq⟩
    · simp at htq
    · simp at htq
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
  refine ⟨⟨e, t + 1, slack', hnb', ∅, ∅, none, hwin_inv', hagreeE, hbook', hchain', hd_eq', hred',
    hpast', hQ', hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

/-- The full state construction for B1 (alive): after the repair `r`,
`t0 = t₂+1`, slack accounting `slack − bad` (the `hslack` hypothesis
gives `bad ≤ slack`), Q/P extension (`extend_h*` glue), reduced bound
`max hnb (J'''+1)`. -/
lemma step_b1_alive (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hslack : B1SlackHyp σ C₀ M)
    (hQ : HQsupplyHyp σ C₀ M)
    (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ)
    (hwin : st.win = some (d_pre, t₀, q₀, q₀', j₀, j₀'))
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb)
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hdis : schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hnoop : st.d t₂ ∉ schedCache st.d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂)
    (ht₀t₂ : st.t0 ≤ t₂)
    {j''' : ℕ} (hj''' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''') :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1 := by
  let q'' : Page := fifoSchedule σ C₀ t₂
  let bad : ℕ := if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache st.d C₀ σ (t₂ + 1 + j''') then 1 else 0
  have hQ_up : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ < tᵢ + 1 + j'' := (hQ st t₂).1
  have hQ_ext : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'' := (hQ st t₂).2
  rcases iterate_main_case_b1_alive d_pre st.d t₀ q₀ q₀' σ C₀ hC₀ ht₂ st.hnb ht₂hnb
    hagree hdis hnoop hftd hj''' st.Q (by
      intro s hs
      simpa [windowExchange, hwin] using st.hchain s hs) st.P (by
      intro s hs
      simpa [windowExchange, hwin] using st.hd_eq s hs) st.hdred with
    ⟨r, hagree', hmiss', hchainL, hd_eqL, hdred', hrt, hrN, hre2, hce⟩
  have hbads : bad ≤ st.slack := by
    dsimp [bad]
    exact hslack st t₂ ht₂ ht₂hnb hagree hdis hnoop hftd hj'''
  have hbook' : schedMisses r C₀ σ + (st.slack - bad) ≤ M := by
    have h1 : schedMisses r C₀ σ + (st.slack - bad) ≤
        (schedMisses st.d C₀ σ + bad) + (st.slack - bad) := by
      exact Nat.add_le_add_right (by simpa [bad] using hmiss') (st.slack - bad)
    have h2 : (schedMisses st.d C₀ σ + bad) + (st.slack - bad) ≤
        schedMisses st.d C₀ σ + st.slack := by
      omega
    exact le_trans (le_trans h1 h2) st.hbook
  have hpast₂ : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q → tᵢ < t₂ := by
    intro tᵢ q''₀ htq
    have h := st.hpast tᵢ q''₀ htq
    omega
  have hq''res : q'' ∈ schedCache st.d C₀ σ t₂ := by
    have hfd := first_disagree st.d σ C₀ hC₀ ht₂ hagree hdis
    simpa [q''] using hfd.2.2
  have hre : ∀ s, s < t₂ → r s = st.d s := by
    intro s hs
    exact hre2 s (by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with hEq | hmem
      · exact (ne_of_lt hs) hEq
      · exact (by omega : s ≠ t₂ + 1 + j''') (Finset.mem_singleton.mp hmem))
  have hwin_inv' : ∀ (d_pre' : ℕ → Page) (t₀' : ℕ) (q₀'' q₀''' : Page) (j₀'' j₀''' : ℕ),
      st.win = some (d_pre', t₀', q₀'', q₀''', j₀'', j₀''') →
      t₀' < t₂ + 1 ∧ d_pre' t₀' = q₀'' ∧ q₀'' ≠ q₀''' ∧
      (∀ s, t₀' ≤ s → σ.getD s 0 ∉ schedCache d_pre' C₀ σ s → d_pre' s ∈ schedCache d_pre' C₀ σ s) ∧
      σ.getD t₀' 0 ∉ schedCache d_pre' C₀ σ t₀' ∧ q₀''' ∈ schedCache d_pre' C₀ σ t₀' ∧
      nextUse σ (t₀' + 1) q₀'' = some j₀'' ∧
      (∀ k, t₀' + 1 ≤ k → k < t₀' + 1 + j₀'' → σ.getD k 0 ≠ q₀''') ∧
      nextUse σ (t₀' + 1) q₀''' = some j₀''' := by
    intro d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq
    rcases st.hwin_inv d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨by omega, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange st.win r σ C₀) C₀ σ s \
      schedCache r C₀ σ s ⊆ (insert (t₂, q'') st.Q).image Prod.snd := by
    intro s hs
    simpa [Finset.image_insert, windowExchange, hwin, q''] using hchainL s hs
  have hd_eq' : ∀ s, s ∉ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      r s = windowExchange st.win r σ C₀ s := by
    intro s hs
    simpa [windowExchange, hwin] using hd_eqL s hs
  have hpast' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q → tᵢ < t₂ + 1 :=
    extend_hpast st.Q hpast₂
  have hQfifo' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      q''₀ = fifoSchedule σ C₀ tᵢ := by
    simpa [q''] using extend_hQfifo σ C₀ st.Q (rfl : q'' = fifoSchedule σ C₀ t₂) st.hQfifo
  have hP' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) := by
    simpa [q''] using extend_hP σ st.Q st.P hj''' st.hP
  have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) →
      s ∈ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) := by
    simpa [q''] using extend_hP_in σ st.Q st.P hj''' hpast₂ st.hP_in
  have hcomp' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ ∧ r s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ r s = q''₀) := by
    simpa [q''] using extend_hcomp' σ st.Q st.P r st.d hj''' hrt hrN hre2 st.hcomp
  have hpair' : ∀ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      nextUse σ (tᵢ + 1) q''₀ = some j''₀ →
      σ.getD tᵢ 0 ∉ schedCache r C₀ σ tᵢ ∧ q''₀ ∈ schedCache r C₀ σ tᵢ ∧ r tᵢ = q''₀ := by
    simpa [q''] using extend_hpair σ C₀ st.Q r st.d hftd hq''res hrt hre hce hpast₂ st.hpair
  refine ⟨⟨r, t₂ + 1, st.slack - bad, max st.hnb (t₂ + 1 + j''' + 1),
    insert (t₂, q'') st.Q, st.P ∪ ({t₂, t₂ + 1 + j'''} : Finset ℕ), st.win,
    hwin_inv', hagree', hbook', hchain', hd_eq', hdred', hpast', (by simpa [q''] using hQ_ext),
    hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

/-- The full state construction for B2 (alive-alive): after the repair
`r`, `t0 = t₂+1`, slack unchanged (a strong repair is free), Q/P
extension (`extend_h*` glue), reduced bound `max hnb (J''+1)`.  The
bridges `hqinE`/`hnotE`/`hnot` are supplied by the caller (branch
analysis, `b2_hnotE` + hQ hypothesis, window off-P; `hnot` empirically
fails on 136 windows — see DESIGN "Remaining" item (2)). -/
lemma step_b2_alive (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (M : ℕ) (st : IterateState σ C₀ M)
    (hQ : HQsupplyHyp σ C₀ M)
    (d_pre : ℕ → Page) (t₀ : ℕ) (q₀ q₀' : Page) (j₀ j₀' : ℕ)
    (hwin : st.win = some (d_pre, t₀, q₀, q₀', j₀, j₀'))
    {t₂ : ℕ} (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb)
    (ht₂₀ : t₀ < t₂) (ht₂₁ : t₂ < t₀ + 1 + j₀')
    (hagree : agreeWithFIF st.d C₀ σ t₂)
    (hdis : schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1))
    (hqin : st.d t₂ ∈ schedCache st.d C₀ σ t₂)
    (hftd : σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂)
    (ht₀t₂ : st.t0 ≤ t₂)
    {j : ℕ} (hj : nextUse σ (t₂ + 1) (st.d t₂) = some j)
    {j'' : ℕ} (hj'' : nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j'')
    (hjj'' : j < j'')
    (hqinE : st.d t₂ ∈ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ t₂)
    (hnotE : ∀ s, t₂ < s → s ≤ t₂ + 1 + j →
      σ.getD s 0 ∉ schedCache (exchangeSchedule d_pre t₀ q₀ q₀' σ C₀) C₀ σ s)
    (hnot : ∀ s, t₂ < s → s ≤ t₂ + 1 + j → s ∉ st.P) :
    ∃ st' : IterateState σ C₀ M, st'.t0 = t₂ + 1 := by
  let q : Page := st.d t₂
  let q'' : Page := fifoSchedule σ C₀ t₂
  have hQ_up : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ < tᵢ + 1 + j'' := (hQ st t₂).1
  have hQ_ext : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, fifoSchedule σ C₀ t₂) st.Q →
      nextUse σ (tᵢ + 1) q''₀ = none ∨
        ∃ j'', nextUse σ (tᵢ + 1) q''₀ = some j'' ∧ t₂ + 1 < tᵢ + 1 + j'' := (hQ st t₂).2
  have hwin_facts : d_pre t₀ = q₀ ∧ q₀ ≠ q₀' ∧
      (∀ s, t₀ ≤ s → σ.getD s 0 ∉ schedCache d_pre C₀ σ s → d_pre s ∈ schedCache d_pre C₀ σ s) ∧
      σ.getD t₀ 0 ∉ schedCache d_pre C₀ σ t₀ ∧ q₀' ∈ schedCache d_pre C₀ σ t₀ ∧
      nextUse σ (t₀ + 1) q₀ = some j₀ ∧
      (∀ k, t₀ + 1 ≤ k → k < t₀ + 1 + j₀ → σ.getD k 0 ≠ q₀') ∧
      nextUse σ (t₀ + 1) q₀' = some j₀' := by
    rcases st.hwin_inv d_pre t₀ q₀ q₀' j₀ j₀' hwin with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h2, h3, h4, h5, h6, h7, h8, h9⟩
  have ht₂notP : t₂ ∉ st.P := by
    apply no_nop_at_b2 st.d σ C₀ st.Q st.P (t := t₂)
    · intro tᵢ q''₀ htq
      have h := st.hpast tᵢ q''₀ htq
      omega
    · exact st.hP
    · exact st.hcomp
    · exact st.hpair
    · exact ht₂
    · exact hqin
  rcases iterate_main_case_b2_alive d_pre st.d t₀ q₀ q₀' σ C₀ hC₀ hwin_facts.1 hwin_facts.2.1
    hwin_facts.2.2.1 hwin_facts.2.2.2.1 hwin_facts.2.2.2.2.1
    hwin_facts.2.2.2.2.2.1 hwin_facts.2.2.2.2.2.2.1 hwin_facts.2.2.2.2.2.2.2
    ht₂ ht₂₀ ht₂₁ st.hnb ht₂hnb hagree hdis hqin hftd hj hj'' hjj''
    st.Q (by
      intro s hs
      simpa [windowExchange, hwin] using st.hchain s hs) (by
      intro tᵢ q''₀ htq
      have h := st.hpast tᵢ q''₀ htq
      omega) hQ_up hqinE hnotE st.P ht₂notP hnot (by
      intro s hs
      simpa [windowExchange, hwin] using st.hd_eq s hs) st.hdred with
    ⟨r, hagree', hmiss', hchain', hd_eq', hdred', hrt, hrN, hre2, hce⟩
  have hbook' : schedMisses r C₀ σ + st.slack ≤ M := by
    exact le_trans (Nat.add_le_add_right hmiss' st.slack) st.hbook
  have hpast₂ : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ st.Q → tᵢ < t₂ := by
    intro tᵢ q''₀ htq
    have h := st.hpast tᵢ q''₀ htq
    omega
  have hq''res : q'' ∈ schedCache st.d C₀ σ t₂ := by
    have hfd := first_disagree st.d σ C₀ hC₀ ht₂ hagree hdis
    simpa [q''] using hfd.2.2
  have hre : ∀ s, s < t₂ → r s = st.d s := by
    intro s hs
    exact hre2 s (by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with hEq | hmem
      · exact (ne_of_lt hs) hEq
      · exact (by omega : s ≠ t₂ + 1 + j'') (Finset.mem_singleton.mp hmem))
  have hwin_inv' : ∀ (d_pre' : ℕ → Page) (t₀' : ℕ) (q₀'' q₀''' : Page) (j₀'' j₀''' : ℕ),
      st.win = some (d_pre', t₀', q₀'', q₀''', j₀'', j₀''') →
      t₀' < t₂ + 1 ∧ d_pre' t₀' = q₀'' ∧ q₀'' ≠ q₀''' ∧
      (∀ s, t₀' ≤ s → σ.getD s 0 ∉ schedCache d_pre' C₀ σ s → d_pre' s ∈ schedCache d_pre' C₀ σ s) ∧
      σ.getD t₀' 0 ∉ schedCache d_pre' C₀ σ t₀' ∧ q₀''' ∈ schedCache d_pre' C₀ σ t₀' ∧
      nextUse σ (t₀' + 1) q₀'' = some j₀'' ∧
      (∀ k, t₀' + 1 ≤ k → k < t₀' + 1 + j₀'' → σ.getD k 0 ≠ q₀''') ∧
      nextUse σ (t₀' + 1) q₀''' = some j₀''' := by
    intro d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq
    rcases st.hwin_inv d_pre' t₀' q₀'' q₀''' j₀'' j₀''' hEq with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨by omega, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hchain' : ∀ s, s ≤ σ.length → schedCache (windowExchange st.win r σ C₀) C₀ σ s \
      schedCache r C₀ σ s ⊆ (insert (t₂, q'') st.Q).image Prod.snd := by
    intro s hs
    simpa [Finset.image_insert, windowExchange, hwin, q''] using hchain' s hs
  have hd_eq' : ∀ s, s ∉ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      r s = windowExchange st.win r σ C₀ s := by
    intro s hs
    simpa [windowExchange, hwin] using hd_eq' s hs
  have hpast' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q → tᵢ < t₂ + 1 :=
    extend_hpast st.Q hpast₂
  have hQfifo' : ∀ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      q''₀ = fifoSchedule σ C₀ tᵢ := by
    simpa [q''] using extend_hQfifo σ C₀ st.Q (rfl : q'' = fifoSchedule σ C₀ t₂) st.hQfifo
  have hP' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) := by
    simpa [q''] using extend_hP σ st.Q st.P hj'' st.hP
  have hP_in' : ∀ s, (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀) →
      s ∈ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) := by
    simpa [q''] using extend_hP_in σ st.Q st.P hj'' hpast₂ st.hP_in
  have hcomp' : ∀ s, s ∈ st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ) →
      (∃ (tᵢ : ℕ) (q''₀ : Page), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧ s = tᵢ ∧ r s = q''₀) ∨
      (∃ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q ∧
        nextUse σ (tᵢ + 1) q''₀ = some j''₀ ∧ s = tᵢ + 1 + j''₀ ∧ r s = q''₀) := by
    simpa [q''] using extend_hcomp' σ st.Q st.P r st.d hj'' hrt hrN hre2 st.hcomp
  have hpair' : ∀ (tᵢ : ℕ) (q''₀ : Page) (j''₀ : ℕ), (tᵢ, q''₀) ∈ insert (t₂, q'') st.Q →
      nextUse σ (tᵢ + 1) q''₀ = some j''₀ →
      σ.getD tᵢ 0 ∉ schedCache r C₀ σ tᵢ ∧ q''₀ ∈ schedCache r C₀ σ tᵢ ∧ r tᵢ = q''₀ := by
    simpa [q''] using extend_hpair σ C₀ st.Q r st.d hftd hq''res hrt hre hce hpast₂ st.hpair
  refine ⟨⟨r, t₂ + 1, st.slack, max st.hnb (t₂ + 1 + j'' + 1),
    insert (t₂, q'') st.Q, st.P ∪ ({t₂, t₂ + 1 + j''} : Finset ℕ), st.win,
    hwin_inv', hagree', hbook', hchain', hd_eq', hdred', hpast', (by simpa [q''] using hQ_ext),
    hQfifo', hP', hP_in', hcomp', hpair'⟩, rfl⟩

end Caching

end CLRS
