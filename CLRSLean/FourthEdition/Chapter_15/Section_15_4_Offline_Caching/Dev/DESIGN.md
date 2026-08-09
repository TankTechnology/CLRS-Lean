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

## B5 iteration details (working notes)

State: `(d, t0, hnb, slack)`, invariants: `agreeWithFIF d t0`,
`∀ s ≥ hnb, fault s → d s resident`, `schedMisses d + slack ≤ M`.

Each step finds the first disagreement `t > t0` (`exists_first_disagree_after`:
`agree d t0` + not `agree d (σ.length)` ⇒ `∃ t ∈ (t0, σ.length)`, `agree d t`,
`¬ agree d (t+1)`; search by descending induction from `σ.length`, since
`agree d 0` always holds).  Then:

- **case A: `t ≥ hnb`** — exchange via `exchange_step'` (hweak from `t`
  only; `exchange_step` in S3 is the full-reduced special case).  New
  reducedness bound `max hnb (J' + 1)` by `exchangeSchedule_reduced_after`
  (needs `j ≤ j'`, from `fifo_nextUse_order`).  Slack `+1` iff the bad event
  did not occur (`exchangeSchedule_misses_le_plus_one`; `q'` never requested
  again, or `d` evicts `q'` before its first request).
- **case B: `t < hnb`** — repair; both `repair_step` (no-op, B1) and
  `repair_step_swap` (resident, B2) give `misses ≤ e + 1`, so slack `−1`
  (requires `slack ≥ 1`).  New bound `max hnb (J' + 1)` (B1: repair's cache
  equals `e`'s after `J'` by `repairSchedule_superset`; B2: contains it by
  `repairSchedule_superset_swap`).

Slack supply: `t < hnb` puts `t` inside the window of the previous exchange
(whose `q'`/`J'` set `hnb`).  Inside that window the exchange schedule's
eviction at a fault is resident, or equals the previous `q'` (decision
branch 1 — the only no-op branch, since `q' ∉` exchange cache there).  So
`ex t = q'` (B1) implies the *source* schedule evicted `q'` at `t`, i.e. the
bad event did not occur — the previous exchange produced the slack.  A B2
subtraction case (`e` evicts `q` inside `(t, J]`) also traces back to a
no-op eviction of the window's swap page by the source schedule, again a
bad-event-did-not-occur exchange.  Each window has at most one *real*
eviction of `q'` (after it, `q' ∉ E` until `J'`), so the accounting
(bad-event exchanges supply slack; repairs consume it) is sound; the
iteration still needs the precise one-to-one bookkeeping in Lean.

Boundary case: the first disagreement landing exactly on the previous `J'`
request — the exchange faults there (evicting `q'` as a no-op) and reloads
`q'`, so caches coincide with the source afterwards.

Case one (`nextUse q' = none`, `q'` never requested again): the exchange
decision then agrees with `d` everywhere except at `t` (branch 4 never
fires — requests of `q'` never happen and requests of `q` find `d` faulting
by `swap_q_not_mem`; branch 6 never fires because `d s ∈ E ⊆` exchange
cache), so the exchange is `d` with the eviction at `t` swapped.  Branch 1
(`d s = q'`) evicts `q'` as a no-op for the exchange — the exchange is *not*
reduced there, and `exchangeSchedule_reduced_after` needs `hj'` which does
not exist.  So case one needs its own argument (the slack from
`exchangeSchedule_misses_le_plus_one` case A when `q` is requested again;
the never-requested-`q` sub-case needs separate treatment — there the
exchange cache differs from the FIF cache by the never-requested `q`, so
agreement is unattainable and the iteration target must be reconsidered).
This is the remaining obstacle in the iteration assembly.

Termination: `t` strictly increases each step, so at most `σ.length + 1`
steps; induction on `σ.length − t0`.

## B5 current status

Proved in `Dev/B5_Iteration.lean` (all kernel-checked, no sorry), twelve
lemmas:

- `exchange_step'`: exchange with reducedness only from `t` on
- `exists_first_disagree_after`: first disagreement in `[t0, σ.length)`
- `exchange_step_full`: case-two exchange step (agreement extends, misses
  not increased, reduced from `J'+1` on)
- `schedMisses_eq_of_cache_diff`: caches differing only by never-requested
  pages ⇒ equal miss counts
- `exchangeSchedule_case_one`: when `q'` (and `q`) are never requested
  again, the exchange differs from `d` only on `{q, q'}`, evictions agree
- `exchangeSchedule_misses_eq_case_one`: case-one exchange has equal misses
- `schedMisses_eq_of_agree`: agreement everywhere ⇒ equal miss counts
- `exchange_step_slack`: case-two exchange with slack bookkeeping (bad
  event did not occur ⇒ slack + 1)
- `repair_q'_never`: repair with `q'` never requested again needs no slack
  (caches differ only by the dead page `q'`)
- `exchangeSchedule_window_evict`: inside the window, a fault of the
  exchange evicts `q'` (branch 1) or a resident page (branches 2-6)
- `evicted_page_absent_until_request`: a true eviction of `q'` keeps it out
  of the cache until `J'` (bad event did not occur — the slack supply step)

Remaining: the iteration induction itself (`iterate_main`, induction on
`σ.length − t0`), needing:
1. case A assembly: `exchange_step_slack` + `exchange_step_full` (reduced
   bound `J'+1`), case-one via `exchangeSchedule_misses_eq_case_one`;
2. case B integration — the slack chain is now complete:
   `window_branch1_once` (branch 1 happens at most once per window) rules
   out later no-op branch-1 positions entirely, so a case-B branch 1 is
   always the first one: a true eviction ⇒ `evicted_page_absent_until_request`
   ⇒ bad event did not occur ⇒ slack ≥ 1;
3. case-B resident (B2) positions: the analysis showed the exchange is
   reduced from any position except the unique branch-1 spot `s₁`, so a B2
   position before `s₁` cannot use `exchange_step'` (the future `s₁` breaks
   hdred), and `repair_step_swap` would need either slack (none available
   for the second consumer) or the strong version (misses ≤ e), whose
   "keep swap" premise still needs the multi-set `q` case analysed.  The
   clean fix is to track the window parameters (`q'`, `J'`, the branch-1
   spot) in the iteration state, or to prove a "reduced except finitely
   many points" form; this is the remaining obstacle;
4. the boundary case at the previous `J'` (exchange faults there, reloads
   `q'`, after which the difference from the FIF cache is a never-requested
   page — the `schedMisses_eq_of_cache_diff` completion argument);
5. `fifo_optimal` assembly and the verification/merge pass.

## B2 resident positions: concrete analysis (2026-08-10)

A concrete example was constructed showing the `t₂ < s₁` case-B resident
(B2) position really occurs:

`σ = [1,2,3,4,5,1]`, `C₀ = {1,2}`, `d₀` evicts 2 at 2, 3 at 3, 1 at 4.
- FIF at 2 evicts farthest of {1,2} = 1 (requested again at 5): `q' = 1`,
  `J' = 5`, window `(2, 5]`.
- Position 3: exchange evicts 3 (branch 5), FIF evicts 2 — disagreement at
  3, a B2 position with the branch-1 spot `s₁ = 4` still in the future.

So both orderings of B2 positions vs the branch-1 spot are possible, and
the remaining obstacles are exactly:

1. **B2 before `s₁`**: the exchange is not reduced from `t₂` on (the future
   branch-1 spot breaks hdred), so `exchange_step'` is unavailable; repair
   needs slack that is already committed to the branch-1 repair.  Needs
   either window-parameter tracking (state carries `q'`, `J'`, the branch-1
   spot) or a "reduced except finitely many points" form.
2. **B2 with `q` never requested again**: `repair_step_swap` needs
   `hj` (q's next use), which does not exist — a dead-page analogue of
   `repair_q'_never` for the swapped page `q` is needed.
3. **Multi-set `q`**: a branch-4/6 eviction can choose a page `q ∈ C' \ E`
   (exchange-only page); the swap-keeping premise of the B2 strong version
   then needs `q ∈ E` until `J₂` (true for branch-5 q's — `q ∈ d₀ cache`
   from reducedness and no earlier eviction — but not automatic for
   multi-set choices).
4. **Branch 5 never re-evicts a branch-5 q**: for `q = d₀ t₂` with a next
   use, `swap_q_not_mem` gives `q ∉ d₀ cache s` on `(t₂, J₂]`, so
   `d₀ s = q` is impossible for the reduced source — branch 5 is excluded
   for requested-again q's.

The clean fix is item 1 (track window parameters in the iteration state);
items 2-4 then become small lemmas.  This is the remaining work before
`iterate_main` can be assembled.

## File layout

- `Dev/B2_Dev.lean` (done): `first_disagree_fault`, `after_J_rel1/rel2`,
  `repairSchedule_after_J`.
- `Dev/B3_AfterJ_Window.lean` (done): generic step + `(J, J']` window.
- `Dev/B4_Repair_Swap_Count.lean` (done): `repairSchedule_superset_swap`,
  `repair_step_swap`.
- `Dev/B5_Iteration.lean` (in progress): the eight lemmas above; next the
  iteration induction, then `fifo_optimal`; then verification (axioms,
  `lake build CLRSLean`, `check_repository.py`, docs, progress CSV) and
  merge of all `Dev/` lemmas into `S3_Optimality.lean`.
