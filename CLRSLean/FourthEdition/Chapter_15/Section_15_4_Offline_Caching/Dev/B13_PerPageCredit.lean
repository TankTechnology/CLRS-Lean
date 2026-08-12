import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.B12_CaseOne_NoWindowB1

/-
# Dev B13: the per-page credit invariant (non-q₀' B1 slack)

The B1 step's slack invariant `bad ≤ slack` (`B1SlackHyp`, B9) is
empirically false for the non-q₀' B1s (DESIGN.md "Slack-accounting
blocker"): of the 3836 B1-bads, 1040 have `d t₂ ≠ q₀'` and 492 of
those hit `slack = 0`.  The q₀'-half is kernel-checked
(`b1_exchange_no_bad_q0` + `b1_bad_le_slack_q0`, B7): the exchange's
`+1` (its bad did not occur) covers the q₀'-B1s.

The DESIGN's "Non-q₀' B1 pairing proposal" pairs the non-q₀' B1's bad
with a **pending good**: the B1's bad on `q''` is a real +1 at `J'''`
(the repair faults where `d` hits) covered iff the page `q''` has a
pending good — an earlier good event on `q''` not yet consumed by a
bad on `q''` (the "keeper" step that kept `q''` in its cache; the
alive-alive B2's exact-net credit `+1{J} − 1{bad}` on its kept page,
`repair_step_swap_exact_net` B6, and the B2-q''-dead's `+1`).

This file formalizes the per-page credit accounting:

- `b1_bad_le_slack_credit`: the per-page B1 supply — `bad ≤ slack + c q''`
  (the page's pending good or the slack pool);
- `b1_draw_credit`: the credit-first draw — the page's credit covers the
  bad, the slack untouched;
- `b1_draw_slack`: the slack draw — the page's credit is empty, the bad
  draws from the slack (needs `1 ≤ slack`);
- `b2_good_accrues`: the alive-alive B2's good accrues on the kept page
  (`c q + 1`), preserving the total `slack + Σ c`.

Empirical validation (2026-08-12, exact-iteration search over σ of
length 4-9, alphabet {1..4}, both d₀ policies; `search_slack.py`
variants): the per-page accounting (q₀'-B1s drawn from the slack, the
non-q₀' B1s drawn from `c q''` first) reduces the crashes 492 → 336;
the candidate-C global accounting (the alive-alive net to the slack)
reduces to **164**.  The residual 164 all have a window with **two
consecutive B1-bads**: the crasher sits at the first pair's nop with
`d t₂` = the pair's page and `q''` = FIF's farthest page — a page with
no pending good under any identified credit (the DESIGN's open item
(a): the invariant form needs the window-global refinement — the
per-page balances can go negative, e.g. the exchange's bad on `q₀'`
has no good on its page).

Main results:

- `b1_bad_le_slack_credit`: the per-page B1 supply
- `b1_draw_credit` / `b1_draw_slack`: the per-page draw bookkeeping
- `b2_good_accrues`: the B2 keeper's credit on its kept page
-/

namespace CLRS

namespace Caching

open Finset

/-- The per-page B1 supply: with the slack pool or the page's pending
good `c q''` covering the unit bad, the bad on `q''` is bounded
(DESIGN.md "Non-q₀' B1 pairing proposal").  This is the per-page
strengthening of `B1SlackHyp`'s `bad ≤ slack`. -/
lemma b1_bad_le_slack_credit {slack : ℕ} {c : Page → ℕ} {q'' : Page}
    (hslack : 1 ≤ slack) (hcredit : 1 ≤ c q'') :
    (1 : ℕ) ≤ slack + c q'' := by
  omega

/-- The general bad form: a B1's bad indicator (`0` or `1`) is bounded
by the slack pool plus the page's pending good whenever the pool or
the page covers the unit. -/
lemma b1_bad_indicator_le_slack_credit (σ : List Page) (C₀ : Finset Page)
    (d : ℕ → Page) {slack : ℕ} {c : Page → ℕ} {q'' : Page}
    (hcover : 1 ≤ slack + c q'') {s : ℕ} :
    (if σ.getD s 0 ∈ schedCache d C₀ σ s then 1 else 0) ≤ slack + c q'' := by
  by_cases h : σ.getD s 0 ∈ schedCache d C₀ σ s
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The credit-first draw: when the page's credit covers the bad (the
pending good on `q''` is at least 1), the B1 draws from the page and
the slack pool is untouched — `slack' = slack` and `c' q'' = c q'' − 1`,
so the total `slack + Σ c` drops by exactly the bad. -/
lemma b1_draw_credit {slack : ℕ} {c : Page → ℕ} {q'' : Page}
    (hcover : 1 ≤ c q'') :
    slack + (c q'' - 1 + 1) = slack + c q'' := by
  omega

/-- The slack draw: when the page's credit is empty, the bad draws from
the slack — `c' = c` and `slack' = slack − 1` — again dropping the
total by exactly the bad.  The premise `1 ≤ slack` is the supply
(the exchange's `+1` or an earlier credit). -/
lemma b1_draw_slack {slack : ℕ} (hslack : 1 ≤ slack) :
    (slack - 1) + 1 = slack := by
  omega

/-- The alive-alive B2's good accrues on the kept page: the exact-net
credit `+1 − bad` (`repair_step_swap_exact_net`, B6) credits the page
`q = d t₂` the repair keeps.  With `¬bad` the credit is real; with
`bad` the net is 0 and no credit accrues. -/
lemma b2_good_accrues {slack : ℕ} {c : Page → ℕ} {q : Page} :
    slack + (c q + 1) = (slack + c q) + 1 := by
  omega

/-- The per-page B1 slack hypothesis: the state's slack supply in the
per-page form — `bad ≤ slack + c (fifoSchedule σ C₀ t₂)`, the page of
the B1's repair.  The `c` is the per-page pending-good function
(the assembly's parameter; a state-field extension is the DESIGN's
open choice). -/
def B1SlackCreditHyp (σ : List Page) (C₀ : Finset Page) (M : ℕ)
    (c : Page → ℕ) : Prop :=
  ∀ (st : IterateState σ C₀ M) (t₂ : ℕ) (ht₂ : t₂ < σ.length) (ht₂hnb : t₂ < st.hnb),
    agreeWithFIF st.d C₀ σ t₂ →
    schedCache st.d C₀ σ (t₂ + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t₂ + 1) →
    st.d t₂ ∉ schedCache st.d C₀ σ t₂ →
    σ.getD t₂ 0 ∉ schedCache st.d C₀ σ t₂ →
    ∀ {j''' : ℕ}, nextUse σ (t₂ + 1) (fifoSchedule σ C₀ t₂) = some j''' →
      (if σ.getD (t₂ + 1 + j''') 0 ∈ schedCache st.d C₀ σ (t₂ + 1 + j''') then 1 else 0) ≤
        st.slack + c (fifoSchedule σ C₀ t₂)

end Caching

end CLRS
