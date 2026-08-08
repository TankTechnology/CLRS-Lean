# Dev notes: iteration state machine for `fifo_optimal` (§15.4 S3)

Working design for the remaining proof, kept in `Dev/` until merged into
`S3_Optimality.lean`.  Small files, one lemma group each, committed often.

## Goal

`fifo_optimal (π : Policy) (C₀ : Finset Page) (σ : List Page) :
    misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ`

Via `schedMisses_policySchedule` this reduces to comparing `schedMisses` of
`fifoSchedule` against that of the arbitrary reduced schedule
`d₀ = policySchedule π C₀ σ` (reduced because `Policy.evict_mem` forces
resident evictions at faults).

## Iteration state machine

Start from `(d₀, hnb=0, slack=0)`; invariants:
- **I-agree**: `agreeWithFIF d t` for the current agreement bound `t`
  (positions `≤ t` agree with the FIF schedule)
- **I-reduced**: `∀ s ≥ hnb, fault s → d s ∈ cache s`
- **I-book**: `schedMisses d + slack ≤ schedMisses d₀`

Each step finds the first disagreement `t₂ > t` (fault at both sides by
`first_disagree`).  Cases:

- **A — `t₂ ≥ hnb`, resident**: exchange at `t₂`.
  - `exchange_step`: misses not increased, agreement extends to `t₂+1`.
  - `exchangeSchedule_reduced_after`: new bound `max hnb (J' + 1)` (needs
    `hq'ne`, which follows from `fifo_nextUse_order`: `j ≤ j'`).
  - Slack: `+1` if the bad event did not occur
    (`exchangeSchedule_misses_le_plus_one`; `q'` never requested again, or
    `d` evicts `q'` before its first request), else `+0`.
- **B1 — `t₂ < hnb`, no-op (`d t₂ ∉ cache`)**: repair at `t₂`
  (`repair_step`, in S3): misses ≤ +1 (paid from slack, so requires
  `slack ≥ 1`), agreement extends to `t₂+1`.  This is the only case that
  consumes slack.  It occurs only when the previous exchange evicted `q'`
  early (`d t₂ = q'`), which guarantees the bad event did not occur — so the
  previous exchange produced the required slack.
- **B2 — `t₂ < hnb`, resident (`d t₂ ∈ cache`)**: repair with the swap
  machinery.  `repair_step_swap` (Dev/B4) shows misses are **not increased**
  at all (good event at `J = t₂ + 1 + j` offsets the bad event at
  `J' = t₂ + 1 + j'`), so no slack is needed.

Both repair cases: after `J'`, `repair`'s cache contains `e`'s
(`repairSchedule_superset`), so the reducedness bound becomes
`max hnb (J' + 1)` again; in B2 the analogue of `repairSchedule_superset`
may be needed (or a subset-version derived from the B2 window).

Termination: each step extends agreement by at least one position, so at
most `σ.length + 1` steps; the final schedule agrees everywhere, hence its
miss count equals `schedMisses (fifoSchedule)`, and the invariant gives
`schedMisses (fifoSchedule) ≤ schedMisses d₀`.

## Window lemmas (B2 machinery)

`repairSchedule e t q' (t+1+j')` evicts `q'` at `t` and at `J'`, follows `e`
elsewhere.  For the resident case (`q = e t`, `j < j'`):

- `(t, J]` window (`repairSchedule_window_swap'`, S3):
  `cache s = insert q (E_s − q')` — actually the two-way statement,
  swap-or-subtraction.
- `J+1` after the good event (`repairSchedule_after_J`, Dev/B2):
  subtraction or `∃ x, insert x (E_{J+1} − q')`.
- **(J, J'] window (Dev/B3, remaining)**: by induction,
  `cache s = (E_s − q') ∨ ∃ x, insert x (E_s − q')`.  Single step: generalize
  `rel1`/`rel2` to arbitrary swap page `x` and arbitrary request `r`, with
  `r ≠ q'` from `getD_ne_nextUse` (`s < J'`).

Consequences used by the counting lemma (B4):

- Bad events in `(t, J']` are confined to `J'`:
  `E_s − cache s ⊆ {q'}` (requests `≠ q'` inside the window can only be bad
  if `q'` is the requested page; the subtraction/swap forms show
  `E_s − cache s ⊆ {q'}`; the only `q'` request is at `J'`).
- Good event at `J`: `q ∈ cache J`, `q ∉ E_J` (`swap_q_not_mem`), so the
  repair hits where `e` faults.
- At `J'`: `q' ∉ cache J'` (window), so the repair faults; `e` hits there
  iff it never evicted `q'` early.

Hence pointwise `rF s ≤ eF s + (if s = J' then 1 else 0) − (if s = J then
1 else 0)`, summing to `schedMisses r ≤ schedMisses e`.

## File layout

- `Dev/B2_Dev.lean` (done): `first_disagree_fault`, `after_J_rel1/rel2`,
  `repairSchedule_after_J`.
- `Dev/B3_AfterJ_Window.lean` (next): generic step + `(J, J']` window.
- `Dev/B4_Repair_Swap_Count.lean`: `repair_step_swap`.
- `Dev/B5_Iteration.lean`: state machine + `fifo_optimal`; then verification
  (axioms, `lake build CLRSLean`, `check_repository.py`, docs, progress CSV)
  and merge of all `Dev/` lemmas into `S3_Optimality.lean`.
