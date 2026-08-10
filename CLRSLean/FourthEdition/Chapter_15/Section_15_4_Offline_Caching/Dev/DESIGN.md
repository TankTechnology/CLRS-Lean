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

## B2 resident positions: concrete analysis (2026-08-10, corrected)

**The example recorded earlier was wrong.**  `σ = [1,2,3,4,5,1]` was claimed
to make FIF evict page 1 at position 2 (`q' = 1`, `J' = 5`).  Under the real
`Farther` semantics (`none` = never requested again is the *farthest*),
`nextUse σ 3 1 = some 5` while `nextUse σ 3 2 = none`, so FIF evicts page 2
at position 2.  The claimed trace does not occur.  (Verified by
`Dev/search_b2.py`, which mirrors the Lean semantics exactly.)

**A genuine B2-before-s₁ trace does exist** (found by exhaustive search,
verified by `search_b2.py`):

`σ = [1,1,3,2,1,2,4,2,3]`, `C₀ = {1,2}`, `d₀` = smallest-resident eviction.

| pos | request | d₁ cache | FIF cache |
|-----|---------|----------|-----------|
| 4   | 1       | {2,3}    | {2,3}     |
| 5   | 2       | {1,2}    | {1,2}     |
| 6   | 4       | {2,4}    | {2,4}     |
| 7   | 2       | {1,4}    | {2,4}     |
| 8   | 3       | {1,2,4}  | {2,4}     |
| 9   | —       | {1,3,4}  | {3,4}     |

- Exchange at `t₀ = 4`: `q₀ = 2` (`d₀ 4 = 2`), `q₀' = 3` (`J₀' = 8`, window
  `(4,8]`).  `d₀` evicts 3 at 7 (its own fault at 7), so the branch-1 spot
  is `s₁ = 7` — **in the future**.
- First disagreement after the exchange: `t₂ = 6 < hnb = 9`, and
  `d₁ 6 = 2 ∈ cache 6` — a **B2 position before s₁**.  FIF evicts `q'' = 1`
  at 6, which is **never requested again** (dead).
- The strong repair `r` (evict `q'' = 1` at 6, keep `q = 2`) hits at
  `J = 7` where `d₁` faults (the good event): `r` has **3 misses vs 4** for
  `d₁` — the repair is free and even *saves* one.  The branch-1 no-op at 7
  evicts `q₀' = 3 ≠ q`, so the swap form survives through `s₁`.

The second search hit `σ = [1,1,3,2,1,4,1,2,3]` exercises the alive-alive
case: B2 at `t₂ = 5` with `q = 1`, `q'' = 2` (`J'' = 7`), good event at
`J = 6`, bad event at `J'' = 7` — `rF = eF + 1 − 1 = eF`, free.

### Refined B2 design: the strong repair needs no slack and no s₁

The previous "obstacles" list is revised by the analysis above:

1. **B2 before `s₁` is handled by the strong repair, not the exchange.**
   The exchange route is indeed blocked (`hdred` fails at the future `s₁`),
   but the repair route does not need `s₁` at all.  `repair_step_swap_strong`
   (to be proved in `Dev/B6_Strong_Repair.lean`) replaces the weak bound
   `rF ≤ eF + 1{J''}` by `rF ≤ eF + 1{J''} − 1{J}`: the good event at
   `J = t₂+1+j` (repair hits where `e` faults — `swap_q_not_mem`) offsets
   the bad event at `J'' = t₂+1+j''`.  Its only extra hypothesis is the
   **keep-swap form at `J`**:
   `Ŝ_J = insert q (E_J − q'')`.
2. **Keep-swap holds in the iteration context.**  The form survives iff
   `e` never evicts `q` on `(t₂, J]`.  Since `q ∉ E_s` on `(t₂, J]`
   (`swap_q_not_mem`), an eviction `e s = q` would be a no-op, and the only
   no-op evictions in the current window evict the window page `q₀'` (branch
   1, `exchangeSchedule_window_evict`) or a past repair's page `q''ₖ` (a
   repair nop).  Both are `∉ E_{t₂}` (window / nop-range facts), while
   `q ∈ E_{t₂}` (B2 resident), so none can equal `q`.  **The state needs the
   current window's page `q₀'` (and the exchange's parameters `t₀`, `q₀`)
   to instantiate the window lemmas — but not `s₁`.**
3. **Dead-page sub-cases** (obstacle 2, sharpened).  `nextUse q` and
   `nextUse q''` need not both exist:
   - *q dead* ⟹ *q'' dead* (new, verified): `q''` is the farthest page and
     `none` is the farthest, so `farthestInFuture_max` forces `nextUse q'' =
     none`.  Hence the q-dead case always has both pages dead: `r` differs
     from `e` only on `{q, q''}` (a fully general cache-diff induction,
     `repair_cache_diff` — no keep-swap, no reducedness needed), both dead,
     so `schedMisses r = schedMisses e` (`repair_step_swap_q_dead`),
     **free**.
   - *q alive, q'' dead*: the repair has no `nop`; `r` saves exactly 1 at
     `J` (good event, no bad event): `rF = eF − 1`, **free** — verified on
     the search's first trace.  (To be formalized after the strong version.)
4. **Multi-set q (obstacle 3, resolved — a false alarm)**.  The fear was
   that a branch-4/6 eviction could choose the B2's `q` from `C' \ E`.  It
   cannot: `q = e t₂` is the exchange's own eviction at `t₂`, so `q ∉ C'`
   on `(t₂, J₂]` — and `swap_q_not_mem` gives `q ∉ E_s = C'_s` directly
   (the exchange's cache *is* `E`).  Every branch of `exchangeDecision` at
   a fault `s ∈ (t₂, J₂]` evicts either `q₀'` (branch 1 — `q₀' ≠ q` by
   `exchangeSchedule_q'_absent` + resident `q`), a page of `C'` (branches
   4-6 — not `q`), or `d s` (branch 5 — `d s = q` would contradict
   `q ∉ C'`).  So `e s ≠ q` on `(t₂, J₂]` (`exchange_no_evict_q`), and the
   swap form survives to `J₂` — the keep-swap derivation
   (`repair_keep_swap`) needs no multi-set analysis.
5. **Branch 5 never re-evicts a branch-5 q** (obstacle 4): unchanged —
   `swap_q_not_mem` gives `q ∉ E` on `(t₂, J₂]`, so `e s = q` is impossible;
   subsumed by `exchange_no_evict_q`.

So the extended iteration state is: `(d, t0, hnb, slack, t₀, q₀, q₀', J₀')`
— the exchange's parameters of the current window (set by case A, untouched
by case-B repairs).  `s₁` needs no tracking for the B2 route; it is only
needed for the B1 slack-supply argument, which is already proven
(`window_branch1_once` + `evicted_page_absent_until_request`).

### B2 step assembly (2026-08-10, verified by `search_b2.py`)

At a B2 position `t₂` inside the window of the exchange at `t₀`, with
`q = e t₂`, `q'' = fifoSchedule σ C₀ t₂`, `j`, `j''`:

- **alive-alive** (`hj`, `hj''`): `repair_step_swap_strong` (B6) gives
  `schedMisses r ≤ schedMisses e` with the keep-swap hypothesis
  `Ŝ_J = insert q (E_J − q'')`; `repair_keep_swap` (B6) derives it from the
  window context (`exchange_no_evict_q` + `repairSchedule_base_swap` +
  the swap-form induction).  **No slack, no s₁.**
- **q dead**: `repair_q_dead_qp_dead` (q dead ⟹ q'' dead) +
  `repair_step_swap_q_dead` (diff ⊆ {q,q''}, both dead):
  equal misses.  **Free.**
- **q alive, q'' dead**: `rF = eF − 1`.  **Free.** (TODO: formalize.)
- The boundary case (the next disagreement landing on `J₀'` itself, the
  previous window's request) is handled by the existing case-A machinery
  (`t ≥ hnb` after the window ends).

**Done (2026-08-10, `Dev/B6_Strong_Repair.lean`, all kernel-checked, no
sorry)**: `getD_ne_of_nextUse_none`, `repair_q_dead_qp_dead`,
`repair_cache_diff`, `repair_step_swap_q_dead`, `repair_step_swap_strong`,
`exchange_no_evict_q`, `repair_keep_swap`, and the q-alive-q''-dead
variant (`repair_cache_diff_le`, `repair_cache_diff_after`,
`repair_step_swap_qp_dead` — pointwise `rF ≤ eF`: equality before `J`,
`0 ≤ 1` at the good event, `E_s − Ŝ_s ⊆ {q''}` after `J`).

### Iteration simulation (2026-08-10, `search_b2.py`)

An exact iteration simulator (directly computing every B2's good event
`q ∈ Ŝ_J` and every B1/B2 bad event) over σ of length 4-8, alphabet
{1,2,3,4}, C₀ = {1,2}/{1,2,3}, and both smallest/largest-resident d₀
policies found:

- **0 slack crashes** with exact accounting (each exchange `+1` iff its bad
  event did not occur; each B1 `−1` iff *its* bad event occurs; B2 strong
  and dead-page repairs free);
- **0 keep-swap failures**: `q ∈ Ŝ_J` held for every alive-alive B2, so
  the strong repair is genuinely slack-free in the iteration.

Conservative "B1 always costs 1" accounting does crash (3 traces, e.g.
σ=[1,1,3,2,1,3,2], d₀=max), but every crash trace has the B1's `q'''` a
**dead page** (the repair is free — same argument as the dead-page B2) or
the bad event not occurring.  So the slack bookkeeping must be exact:
B1 costs `1{J'''}` (paid iff `e` hits `q'''` at `J'''`), supplied by the
exchange's `+1` iff its bad event did not occur — the pairing that
`window_branch1_once` + `evicted_page_absent_until_request` give.

Remaining work: `iterate_main` with the extended state carrying the
exchange's window parameters `(t₀, q₀, q₀', J₀')` and the repair history
pages `W = {q₁, q''₁, …, qₖ, q''ₖ}` (the cache-diff chain needed to
instantiate `exchange_no_evict_q` at later B2 positions: `q ∈ E_t` from
`q ∈ E'_t` plus the diff), then `fifo_optimal` and the merge pass.

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
