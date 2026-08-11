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
- **q alive, q'' dead**: `repair_step_swap_qp_dead` (B6) — pointwise
  `rF ≤ eF` (equality before `J`, `0 ≤ 1` at the good event, superset
  argument after `J`).  **Free.**
- The boundary case (the next disagreement landing on `J₀'` itself, the
  previous window's request) is handled by the existing case-A machinery
  (`t ≥ hnb` after the window ends).

**Done (2026-08-10/11, `Dev/B6_Strong_Repair.lean` +
`Dev/B7_Iteration.lean`, all kernel-checked, no sorry)**:
`getD_ne_of_nextUse_none`, `repair_q_dead_qp_dead`, `repair_cache_diff`,
`repair_step_swap_q_dead`, `repair_step_swap_strong`, `exchange_no_evict_q`,
`repair_keep_swap`; the q-alive-q''-dead variant (`repair_cache_diff_le`,
`repair_cache_diff_after`, `repair_step_swap_qp_dead`); the keep-swap for
the dead-page repair (`repairSchedule_base_swap_qp_dead`,
`repair_keep_swap_qp_dead`, `b2_hswap_qp_dead` — the swap form at `J` for
nop = `t₂`, giving the good event without `hj''`); the reverse-diff chain
extensions (`reverse_diff_chain_qp_dead`, `reverse_diff_chain_q_dead`);
the B1 dead-page repair (`repair_diff_noop_qp_dead`, `repair_step_qp_dead`
— no-op eviction with `q''` dead is free, bad event impossible); and the
shared helpers (`repair_requests_avoid_q_qp`,
`schedCache_repairSchedule_eq_e_qp_dead`, `swap_q_not_mem_dead`).

**Done (2026-08-10/11, second batch, kernel-checked)**: the keep-swap for
the repair of the *current* schedule (`repair_keep_swap_cur`, B7), the
case-B2 alive-alive step (`iterate_main_case_b2_alive` — agreement,
misses, chain, `hd_eq`, reducedness), the case-B1 alive step
(`iterate_main_case_b1_alive` — exact miss accounting
`schedMisses r ≤ schedMisses d + bad` for the `slack − bad` bookkeeping)
with its helpers (`repair_diff_noop_window` in B6, `repair_q''_absent`,
`repair_reverse_diff_after_nop` in B7).

**Progress (2026-08-11, second batch, kernel-checked)**: the hQ-strictness
extension chain — `fifo_evict_absent_until_request` (FIF's own eviction stays
out of its cache until the first request), the state fields `hQfifo` (pair
`q''ᵢ` = the FIF eviction at `tᵢ`) and `hP_in` (the producer direction of
`hP`: pair structure -> `s ∈ P`), `nop_position_noop` (at a nop position
`s = tₗ + 1 + jₗ`, `d s ∉ D_s` via `hcomp`'s value + the FIF-absent fact +
agreement), and `past_pair_first_request_after` (the strict `t₂ < J''ᵢ` at
a B2 disagreement: `J''ᵢ < t₂` gives a cache disagreement at `J''ᵢ + 1`
(FIF's eviction `f` leaves `F` but stays in `D`), `J''ᵢ = t₂` gives the
B1-nop against B2-resident).  This unblocks `b2_ehit_ne` at `t₂` for both
the alive and dead B2 paths.

**Progress (2026-08-11, third batch, kernel-checked)**: `iterate_main_case_b1_dead`
— the B1 dead-page step (free: `repair_step_qp_dead` generic in the schedule,
chain via `repair_diff_noop_qp_dead`, reducedness from `hnb` range-restricted
to `s < σ.length` with the new half-2 premise `hdnoevict` (∀ s ≥ hnb,
`d s ≠ q''`) excluding the `d s = q''` no-op-eviction spots) and the dead-page
absent helpers `repair_q''_absent_dead` / `repair_q''_absent_dead_long`
(`q''` stays out of the dead repair's cache).  The `hdnoevict` premise is
derivable from the state by the branch-analysis half 2 (the exchange never
evicts a dead page: `e s ∈ E_s ∪ {q₀'}`, `q'' ∉ E_s ∪ {q₀'}`).

**Progress (2026-08-11, fourth batch, kernel-checked)**:
`repair_keep_swap_cur_qp_dead` — the current-schedule q''-dead keep-swap
(the dead-page analogue of `repair_keep_swap_cur`: nop = `t₂`, `hq''dead`
replaces `hj''`/`hjj''` via `getD_ne_of_nextUse_none` + `hJlen`, base case
`repairSchedule_base_swap_qp_dead`; same `hd_eq`/`hnot`/
`exchange_no_evict_q`/`hnotE`/`b2_ehit` structure).  It supplies
`reverse_diff_chain_qp_dead`'s `hkept` for the B2-q''-dead step.  The
q-dead B2 step needs **no** keep-swap: `repair_step_swap_q_dead` and
`reverse_diff_chain_q_dead` are already generic in the schedule.

**Progress (2026-08-11, fifth batch, kernel-checked)**: the `hnotE`
derivation (`Dev/B8_HnotE.lean` + `Dev/search_hnot.py`).  The DESIGN's
"`q''ᵢ` requested at `nᵢ ≤ s`, kept" mechanism is **empirically false**
(172 of 180 later requests of a pair page have `q''ᵢ ∉ D_s` — the current
schedule re-evicts it, e.g. `σ=[1,1,3,4,1,3,2,3]`, B2 at 6).  The correct
mechanism (0 violations in the same search): at window positions off `P`,
the exchange never hits where the current schedule faults.  Three lemmas:

- `pair_q''_absent_d`: after the repair at `tᵢ` evicts `q''ᵢ`, the page
  stays out of the current cache until its first request `nᵢ` (clean
  induction, request-avoidance only) — the nop no-op-ness and the
  `q''ₖ ≠ q''ᵢ` distinctness at other nops;
- `pair_page_in_D_of_in_E`: the joint E⟹D induction — for every alive past
  pair with `nᵢ < s`, `q''ᵢ ∈ E_s ⟹ q''ᵢ ∈ D_s`.  The step's only obstacle
  is the e-hit-at-d-fault (`σ[s] ∈ E_s − D_s`): the chain pushes `σ[s]`
  into `Q.image`, and the pair analysis (dead / before-`nₗ` / at-`nₗ`-in-P /
  after-`nₗ`-via-the-IH) contradicts it; at an e-fault with `q'' = σ[s]`
  (the request) both caches gain `σ[s]` directly;
- `b2_hnotE`: the assembly — `σ[s] ∈ E_s` ⟹ `σ[s] ∈ Q.image` (chain) ⟹
  dead / `s < nᵢ` / `s = nᵢ` (`hP_in`) / `s > nᵢ` (`pair_page_in_D_of_in_E`
  gives `q''ᵢ ∈ D_s`, contradicting the d-fault).

The induction uses `Nat.strong_induction_on` with the `s−1` step (the
plain `induction s with` succ-intro mis-elaborates the nested ∀ when
∀-typed hypothesis binders are in scope — see B8's commit note).

**Progress (2026-08-11, sixth batch, kernel-checked)**: the case-step
extension glue for the composition invariants — `extend_hpast`,
`extend_hQfifo`, `extend_hP`, `extend_hP_in`, `extend_hcomp`,
`extend_hpair` (alive variants, `P' = P ∪ {t₂, t₂+1+j''}`) and
`extend_hP_dead`, `extend_hP_in_dead`, `extend_hcomp_dead` (dead-page
variants, `P' = P ∪ {t₂}`), all in B7.  Each takes the old state's
invariant over `Q`/`P`/`d` plus the step's facts (`r t₂ = q''`,
`r nop = q''`, `r s = d s` off `{t₂, nop}`, `schedCache r = schedCache d`
up to `t₂`, `σ[t₂]` fault, `q''` resident, `hpast`, `hj''` or
`hq''dead`) and produces the invariant over `Q' = insert (t₂, q'') Q`,
`P'`, and `r`.  The new pair's positions are witnessed by the new pair
itself (the nop witness's `j''₀` is pinned to `j''` by nextUse
uniqueness); a new nop overwriting an old `P`-position is covered by the
new witness.  `extend_hpair` covers both the alive and dead cases (the
dead pair never satisfies the `nextUse = some` premise).  **hQ's
extension is a separate open design problem** (see the next block).

**hQ-extension blocker (2026-08-11, verified by exhaustive search)**:
the state field `hQ` (`∀ (tᵢ, q'') ∈ Q, nextUse = none ∨ ∃ j'', some j''
∧ t0 < tᵢ+1+j''`) **does not hold over the full-history Q** — a pair
whose nop has passed (`nᵢ ≤ t₂+1` at a case-B step) can never satisfy
`t₂+1 < nᵢ` in the new state.  Over σ of length 4-9, alphabet {1..4},
both d₀ policies: 10236 B1 + 688 B2 steps have an old pair with
`nᵢ ≤ t₂`, 212 B1 + 312 B2 steps have `nᵢ = t₂+1`, and **988 B2 steps
are reached from a state whose hQ is already broken** (e.g.
σ=[1,1,4,3,4,2,1], C₀={1,2}, max: B1 at 5 is the pair (3,2)'s nop, then
B2 at 6 with the pair still in Q).  Pruning broken pairs from Q does
**not** work either: the reverse-diff chain `E − D ⊆ Q.image` needs the
full page history — the pruned chain fails 37956× at all positions and
4588× at future positions (e.g. σ=[1,1,3,4,1,2,3,1], C₀={1,2}, min: at
position 6 = the pruned pair's nop, `3 ∈ E_6 − D_6`).  What does hold
(0 violations): at B2 disagreements σ[t₂] is **never** a broken pair's
page, and the e-hit at B2 is 0 — the consumers (`b2_ehit_ne`,
`b2_hnotE`) only ever consult the pair whose page equals the request, and
that pair is never broken.  So the resolution is a design change, not a
proof: either (a) the state carries the full pair history for the chain
**and** a separate "live" set (pairs with `nᵢ > t0`, dead pairs) for
`hQ`, with `b2_ehit_ne`/`b2_hnotE`/`past_pair_first_request_after`
restated over the live set; or (b) the consumers are restated to take the
state's hQ at bound `st.t0` and derive the strict `t₃ < nᵢ` only for the
consulted pair (whose page is the request — never broken empirically, but
the "requested-again at a B2 disagreement" exclusion needs the
last-repair/nop analysis).  Also open: the new pair's own hQ clause needs
`0 < j''` (the new nop `t₂+1+j''` strictly after `t₂+1`); `j'' = 0`
never occurs empirically but is consistent with the step's local
hypotheses (d hits at `t₂+1` on `q''`, FIF faults) — so the assembly
will need either a global argument or a separate boundary case.

**Remaining for `iterate_main`**: the case steps take the bridge hypotheses
`hnot`/`hnotE`/`hqinE`/`ht₂notP` as inputs; the induction must supply them
per step, which needs: (1) the branch analysis — `e s ∈ E_s ∪ {q₀'}` at
exchange faults — **done** (`exchange_evict_mem_or_q'`, B7, kernel-checked):
from `exchangeDecision`'s structure (branch 1 evicts `q₀'`, branches 4-6
and 5 evict pages of `E`; the `else 0` cases excluded by the fault + the
cardinality argument).  This gives `q ∈ E_{t₂}` at B2 once `t₂ ∉ P`
(see (2)); (2) the last-repair/no-nop-at-B2 analysis — gives `t₂ ∉ P`
and the `Q''`-exclusion at window faults (`hnotE`).  **Core done
(2026-08-11, `no_nop_at_b2`, B7, kernel-checked)**: the naive invariant
"every alive nop `nᵢ` is a no-op (`d nᵢ ∉ D_{nᵢ}`)" is **not
maintainable** — counterexample: an old pair with `q''ᵢ = e J` (the new
repair's good-event eviction) stays in the repair's cache after `J`
(`e J ∈ D_J − q'' ⊆ Ŝ_J` by the swap form and reducedness).  The
maintainable formulation is the **value invariant** `hcomp` (every
`P`-position's value is the page of a pair whose `tᵢ` or nop is there,
with the paired `∃` — maintainable since the new repair sets `{t₂, n₂}`
to the new pair's `q''₂`, which satisfies the `∃` even when `n₂`
overwrites an old nop) plus `hpair` (the past-position facts: `σ[tᵢ]`
fault, `q''ᵢ` resident, `d tᵢ = q''ᵢ`, preserved by later repairs since
`tᵢ < t₂` and the caches agree up to `t₂`).  The derivation: `t ∈ P ⟹
t = tᵢ` (contradicts `hpast`) or `t = nᵢ` — the invariant gives `d t =
q''`, and `evicted_page_absent_until_request` gives `q'' ∉ D_t`, so
`d t ∉ D_t`, contradicting B2-resident.  **Done (sixth batch, B7,
kernel-checked)**: the `hcomp`/`hP`/`hP_in`/`hpair`/`hpast`/`hQfifo`
extension glue (the `extend_*` lemmas above); the `hnotE` derivation
(`pair_q''_absent_d`/`pair_page_in_D_of_in_E`/`b2_hnotE`, B8 —
kernel-checked, fifth batch).  **Open**: the hQ extension (see the
hQ-extension blocker above).  Then (3) the dead-page case
steps (B2-q-dead, B2-q''-dead via `repair_keep_swap_cur_qp_dead`,
B1-dead); then the induction (`exists_first_disagree_after` + the case
steps + the window-state threading — note `hj₀` cannot exist when the
case-A had `q₀` dead, so the window state must be conditional or the
unused window hypotheses dropped), then `fifo_optimal`.

### Iteration simulation (2026-08-10, `search_b2.py` + `search_iter.py`)

An exact iteration simulator (directly computing every B2's good event
`q ∈ Ŝ_J` and every B1/B2 bad event; `Dev/search_iter.py`, entry points
`main` / `search2` / `search3`) over σ of length 4-9, alphabet {1,2,3,4},
C₀ = {1,2}/{1,2,3}, and both smallest/largest-resident d₀ policies found:

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

### `iterate_main` design (2026-08-10, second pass — diff invariant refined)

The first design assumed a full cache-diff invariant `cache_d − cache_e ⊆
W = {q₁, q''₁, …}`.  Simulation showed it **fails**: a request that *is* a
repair page (e.g. `σ[s] = q₀`) makes the two schedules' hit/fault status
diverge and the diff "drifts" (page 1 entered the diff in the trace of
σ=[1,1,3,4,2,1,2,3]).  What does hold (verified over 55188 B2 positions,
σ of length 4-9, alphabet {1,2,3,4}, min/max d₀):

- **`e` never hits at a B2 disagreement** (`σ[t] ∉ cache_e_t`, 0 hits);
- **every B2 good event holds** (`q ∈ Ŝ_J`, 0 keep-fails);
- the **reverse diff** `cache_e − cache_d` stays confined to the repair
  pages `Q'' = {q''₁, …, q''ₖ}` (the drift only goes forward: `cache_d −
  cache_e` may grow, `cache_e − cache_d` never).

The refined invariant is therefore **reverse-diff ⊆ Q''**, and it is
*interleaved with the iteration induction* (it is proved at each position
`t` before the step, used to prove `e` misses at `t` (the e-hit lemma:
`σ[t] ∈ cache_e_t` would force `σ[t] ∈ Q''`, but `q''ᵢ` is dead or first
requested at `J''ᵢ`), then to instantiate `exchange_no_evict_q`, then the
repair step extends `Q''` with `q''`).

Supporting lemmas (new, `Dev/B7_Iteration.lean`):

1. `repair_diff_all` (done, 2026-08-10, kernel-checked): with live `q`,
   `q''` and the keep-swap hypothesis `hkept : q ∈ Ŝ_J` (the good event),
   the **reverse** diff `E_s − Ŝ_s` of the repair `r = repairSchedule e t
   q'' (t+1+j'')` against the source `e` is confined by
   `⊆ {q, q''}` at every `s ≤ σ.length`, `⊆ {q''}` on `(J, J'']`, and
   `∅` (i.e. `E ⊆ Ŝ`) after `J''`.
   - up to `J`: `repair_cache_diff_le` (B6), `hdead` from `hj`/`hj''`;
   - base at `J+1`: `e` faults at `J` (loads `q`), `r` hits (`hkept`), and
     `E_J − Ŝ_J ⊆ {q, q''}` (`repair_cache_diff_le` at `J`) with `q ∉ E_J`
     (`swap_q_not_mem`) leaves only `q''` — **no window form needed**;
   - step on `(J, J'')`: only `r s = e s` (`s ∉ {t, J''}`) and
     `σ[s] ≠ q''` (`getD_ne_nextUse hj''`);
   - base at `J''+1`: both sides gain `q''` (r's nop eviction at `J''` is a
     no-op — `q'' ∉ Ŝ` on `(J, J'']`), and `q'' ∉ E − Ŝ` rules out the
     `{q''}` residue of `hw` at `J''`;
   - step after `J''`: `E ⊆ Ŝ` propagates (`r s = e s`).
   **Corrected from the earlier design**: the two caches do *not* coincide
   after `J''` — the **forward** diff `Ŝ − E` picks up `e J` (the page `e`
   evicts at the good event: the window page `q₀'` at a branch-1 spot, or a
   `C'`-page) and drifts (verified: `σ=[1,1,3,1,2,1,3]`, B2 at 4, `eJ = 2
   = q₀'` stays in `Ŝ` forever).  Only the reverse diff is confined — the
   direction the chain uses.
2. `reverse_diff_chain` (done, 2026-08-10, kernel-checked): `cache_e −
   cache_d ⊆ Q''` — repair steps add only `q''` (the repair evicts `q''`
   while `e` keeps it; `q ∉ cache_e` on `(t, J]` since `e` evicts `q` at
   `t`).  Interleaved with `iterate_main`.  Requires the bridge
   `schedCache_repairSchedule_nop_agree` (`j < j''` ⟹ the caches of
   `repairSchedule e t q'' t` and `repairSchedule e t q'' (t + 1 + j'')`
   agree up to `J`) to connect `repair_cache_diff_le` (dead-page form) to
   the live-live repair.
3. `b2_ehit` (done, 2026-08-10, kernel-checked): the single-step local
   invariant — at a B2 disagreement `t` (d faults, chain at `t`),
   `σ[t] ∈ cache_e_t ⟹ σ[t] ∈ Q`.  The contradiction half is `b2_ehit_ne`
   (dead or not-yet-requested past repair pairs exclude `σ[t]` from
   `Q.image Prod.snd`).  Mechanism (verified over 55188 B2 positions,
   `search_iter.py`):
   `σ[t] ∈ cache_e_t ⟹ σ[t] ∈ E_t − D_t ⊆ Q'' ⟹ σ[t] = q''ᵢ` for a past
   repair `i`.  Then `t ≥ J''ᵢ` (first request of `q''ᵢ` after `tᵢ`).
   - `t = J''ᵢ`: `D t = q''ᵢ` (the repair's nop eviction — the last repair
     touching position `t` — and `q''ᵢ ∉ D`-cache on `(tᵢ, J''ᵢ]`) — a
     no-op eviction, so the position is **B1, not B2** — contradiction.
   - `t > J''ᵢ` (`q''ᵢ` requested again): empirically never at a B2
     (re-analysis: 0 occurrences at any disagreement; all 8976 Q-membership
     cases are `t = J''ᵢ` and B1); the formal argument needs the
     "last repair whose nop is at `t`" analysis.
   Empirical: `σ[t] ∈ {past q''ᵢ}` at a disagreement happens 8976×, all at
   `t = J''ᵢ` — all B1, 0 at B2.
4. `b2_no_evict_q` (done, 2026-08-10, kernel-checked): the keep-swap core
   for the current schedule: at a fault `s ∈ (t, J]` of the exchange
   schedule, `d s = e s` (off the past repair/nop positions `P`, via the
   composition invariant `hd_eq` — `hnot` excludes the modified positions;
   empirical: 136 windows contain a past modified position in `(t, J]` and
   12 of those are faults with `d s ≠ e s`, so `hnot` is essential), and
   `e s ≠ q` by `exchange_no_evict_q` (its `hft₂` — the e-hit at `t` —
   derived inside via `b2_ehit` + `b2_ehit_ne` from the chain instance at
   `t`; `hqin : q ∈ cache_e_t` comes from the branch analysis of
   `e t = q`: branch 1 evicts `q₀'` which is `∉ cache_d_t` — `q₀' ∉
   cache_e` on the window, `q₀' ∉ Q''` since `q''ᵢ ≠ q₀'` (`q₀' ∉
   cache_{tᵢ}` while `q''ᵢ` is FIF-resident), and the `q₀'` membership is
   synchronized —; branches 4-6 evict `C'`-pages, branch 5 evicts `d₀ t`
   which is in `C'` by its own premise; empirically `q ∈ E_t` and
   `e t = d t` hold at all 55188 B2 positions).
5. `b2_hswap` (done, 2026-08-10, kernel-checked): the swap form at `J` for
   the current schedule — already proved in B6 as `repair_keep_swap` (the
   iteration context: window of the case-A exchange at `t₀`); instantiated
   with the window hypotheses (no new proof).
6. `iterate_main`: the induction over `σ.length − t0` with state
   `(d, t0, hnb, slack, t₀, q₀, q₀', j₀', Q'')`; case A sets the window
   and `Q'' = ∅`; case B1 (slack −1 iff its bad event occurs — the exact
   accounting validated by simulation), case B2 via
   `repair_step_swap_strong` + `b2_hswap` (alive-alive),
   `repair_step_swap_q_dead` (q dead), `repair_step_swap_qp_dead` (q'' dead);
   then `fifo_optimal` and the merge pass.

Estimated 2-3 focused sessions for items 2-6, then one for the
`fifo_optimal` assembly and the Dev→S3 merge.

## File layout

- `Dev/B2_Dev.lean` (done): `first_disagree_fault`, `after_J_rel1/rel2`,
  `repairSchedule_after_J`.
- `Dev/B3_AfterJ_Window.lean` (done): generic step + `(J, J']` window.
- `Dev/B4_Repair_Swap_Count.lean` (done): `repairSchedule_superset_swap`,
  `repair_step_swap`.
- `Dev/B5_Iteration.lean` (done): the eight lemmas above; next the
  iteration induction, then `fifo_optimal`; then verification (axioms,
  `lake build CLRSLean`, `check_repository.py`, docs, progress CSV) and
  merge of all `Dev/` lemmas into `S3_Optimality.lean`.
- `Dev/B7_Iteration.lean` (in progress): `repair_reverse_diff_window`,
  `repair_reverse_diff_after`, `repair_diff_all`,
  `schedCache_repairSchedule_nop_agree`, `reverse_diff_chain`, `b2_ehit`,
  `b2_ehit_ne`, `b2_no_evict_q`, `b2_hswap`, `b2_hswap_qp_dead`,
  `reverse_diff_chain_qp_dead`, `reverse_diff_chain_q_dead` (done,
  kernel-checked) and `iterate_main_exchange` (the case-A step, done);
  the current-schedule keep-swap (done: `repair_keep_swap_cur` alive-alive,
  `repair_keep_swap_cur_qp_dead` q''-dead; the q-dead step needs none);
  the case-B1/B2 step lemmas (B1-alive, B1-dead, B2-alive done);
  the case-step extension glue (done, sixth batch: `extend_hpast`,
  `extend_hQfifo`, `extend_hP`, `extend_hP_in`, `extend_hcomp`,
  `extend_hpair`, `extend_hP_dead`, `extend_hP_in_dead`,
  `extend_hcomp_dead`); next the hQ-extension design (see the
  hQ-extension blocker above), the wiring of the `extend_*` lemmas into
  the case-step outputs, then the `iterate_main` induction and
  `fifo_optimal`; then verification (axioms, `lake build CLRSLean`,
  `check_repository.py`, docs, progress CSV) and merge of all `Dev/`
  lemmas into `S3_Optimality.lean`.
