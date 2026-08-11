# FIF (farthest-in-future) optimality — proof design

Status: **design stage** (2026-08-08).  Target: CLRS Theorem 15.5
(`fifo_optimal`), the last gap of §15.4.

## Current state

- `S1_Cache_Model.lean` (proved): `Policy`, `Policy.step`, `cacheSeq`,
  `faultAt` / `misses` / `hits`, `nextUse` + `getD_nextUse` facts.
- `S2_Farthest_In_Future.lean` (proved): `Farther`, `farthestInFuture`,
  `fifoPolicy`, `fifo_step_of_mem` / `fifo_step_fault`.
- `S3_Optimality.lean`: stub with `fifo_evicts_resident`, `fifo_step_size`.

## Target theorem

```lean
theorem fifo_optimal (σ : List Page) (C₀ : Finset Page) (hC₀ : C₀.Nonempty)
    (π : Policy) : misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ
```

## Proof structure (standard exchange argument)

Let `F := fifoPolicy σ`.

**Lemma 2 (exchange lemma).**  If a policy `π` has the same caches as `F`
through position `t` (`cacheSeq π C₀ σ s = cacheSeq F C₀ σ s` for `s ≤ t`)
and the caches differ at `t+1`, then there is a policy `π'` whose caches
agree with `F` through `t+1` and with `misses π' ≤ misses π`.

At `t` both fault on `p := σ.getD t 0`, with common cache `C`; `π` evicts
`q`, `F` evicts `q'`, `q ≠ q'`, and (FIF property)
`Farther (nextUse σ (t+1) q') (nextUse σ (t+1) q)` — `q` is requested again
no later than `q'` (in the extended naturals; both `none` possible).

**Construction of `π'`** (the *swap-conjugate* of `π` w.r.t. the pair
`(e := q, f := q')`):
- `swap C := if f ∈ C then insert e (C.erase f) else C` (size-preserving;
  `swap` is an involution on size-`k` caches containing at most one of
  `e, f`; `f ∉ swap C` always).
- `π'.evict i D r := if π.evict i (swap D) r = e then (if f ∈ D then f else e)
  else π.evict i (swap D) r` — the page of `D` corresponding to the page
  `π` evicts from `swap D`.  Validity: `π.evict i (swap D) r ∈ swap D`;
  if it is `e` and `f ∈ D`, `f ∈ D`; if it is `e` and `f ∉ D`, then
  `e ∈ D` (from `e ∈ swap D`); `f ∈ swap D` never happens.
- At `(t, C)`: `swap C = C` (both `e, f ∈ C`), so `π'.evict t C p` swaps
  `π`'s choice `q` to `q'` — exactly the FIF decision; and
  `C_{t+1}^{π'} = (C - {q'}) ∪ {p} = C_{t+1}^F`.

**Simulation invariant.**  `C_s^{π'} = swap (C_s^π)` for all `s ≥ t+1`,
preserved by the conjugate eviction (the key step is the case analysis on
`a = π.evict s (swap(C_s^π)) r` being `e`, `f`, or other — `f` impossible;
`e` case: `b = f` when `f ∈ C_s^{π'}`, else `b = e`; the set identities
`(insert e (C.erase f)).erase f = insert e (C.erase f)` and
`(insert e (C.erase f)).erase e = C.erase f` etc.).

**Miss comparison.**  For any position `s ≥ t` with request `r`:
`r ∈ C_s^{π'} ⟺ r ∈ swap(C_s^π)`; for `r ∉ {e, f}` this equals
`r ∈ C_s^π`; for `r = e`, `e ∈ swap(C_s^π) ⟺ e ∈ C_s^π ∨ f ∈ C_s^π ⊇
{e ∈ C_s^π}` — so whenever `π` hits on `e`, `π'` hits too (and `π'` may
hit where `π` faults).  Hence `faultAt` of `π'` ≤ `faultAt` of `π` at
every position, and `misses π' ≤ misses π`.

**Iteration (Theorem 2).**  Starting from `π`, repeatedly apply the
exchange lemma at the first position where the caches differ (the
agreement prefix strictly grows), terminating after at most `σ.length + 1`
steps with a policy whose caches equal `F`'s on `[0, σ.length]`, so
`misses F ≤ misses π`.  Formalize with well-founded recursion on the
agreement-prefix length, or by strong induction on `σ.length + 1 - t`
(the `firstDiff` position found via `Nat.find`).

## RESOLVED: final design (2026-08-08, second pass)

**The exchange lemma must be proved on a *schedule* model** (a decision
function `d : ℕ → Page` with its own run `schedCache d C₀ σ`), because no
policy of the form "apply π's eviction function to a derived cache"
maintains any useful invariant (verified by hand above).  On schedules the
"copy π's decision" step is constructive.

**Schedule model.**  `schedCache (d) (C₀) (σ) : ℕ → Finset Page`:
`0 ↦ C₀`, `s+1 ↦ if p_s ∈ C_s then C_s else insert p_s (C_s.erase (d s))`.
`schedMisses` likewise.  `policySchedule π C₀ σ s := π.evict s (cacheSeq π C₀ σ s) (σ.getD s 0)`;
bridge: `schedCache (policySchedule π) = cacheSeq π`, and schedMisses = misses.
(erase of an absent page is a no-op, so schedules need not be reduced; the
policies' schedules are reduced by `Policy.evict_mem`.)

**Exchange schedule.**  Given agreement of `d` with `F := fifoPolicy σ` up
to `t` (caches equal), a fault on `p` at `t` with `d` evicting `q` and `F`
evicting `q'` (`q ≠ q'`), define:
```lean
exchangeSchedule d t q q' σ C₀ s :=
  if s ≤ t then d s
  else if q' ∈ schedCache d C₀ σ s then (if d s = q' then q else d s)
  else d s
```
(`s ≤ t`: identical to `d`, so caches agree through `t`; at `t`: evict `q'`
so the cache becomes `(C - {q'}) ∪ {p} = C_{t+1}^F`, agreeing with `F`
through `t+1`; after `t`: follow `d`, except when `d` evicts `q'` — then
evict `q` (which the invariant keeps in `d'`'s cache).)

**Invariant** (holds for all `s ≥ t+1`): `C'_s △ C_s ⊆ {q, q'}`, and
more precisely the state is one of: adjust `C'_s = (C_s - {q'}) ∪ {q}`
(when `q' ∈ C_s` and `d` has not evicted `q'`), coincide `C'_s = C_s`
(after `d` evicted `q'` and before `q'` is re-requested), or `q'`-extra
`C'_s = C_s ∪ {q'}` (after a no-op eviction).  The `d s = q'` step makes
the caches coincide; the "d faults on r ∈ {q,q'} while d' hits" step can
add `d s ∉ {q,q'}` to the symmetric difference — those pages give `-1`
events when requested.

**Miss comparison** (`misses d' ≤ misses d`), the phase structure with
`u` = next request of `q` after `t` (∞ if none), `v` = next request of
`q'` (∞ if none), and `u ≤ v` from the FIF property:
- Before `u`: requests ∉ {q, q'}, faults equal (invariant).
- At `u`: `d` faults on `q` (evicted at `t`, never re-requested before);
  `d'` hits if `q ∈ C_u^{d'}` (adjust state) — a `-1` — or both fault
  (coincide state) — a `0`.
- After `u`: `+1` events occur only when `d'` lacks a requested page of
  `{q, q'}`: `q'` at `v` (once, in adjust state, compensated by `u`'s
  `-1`), and `q` at the first request after a "`d` evicts `q'`" event
  (each such event is followed by a `q'` request where `d'` has `q'` —
  a `-1`; `+1` events ≤ `d`-evicts-`q'` events ≤ `q'`-request events).
  `-1` events also come from pages `d` evicted while `d'` kept them.
  Hence the total difference is ≤ 0.

**Iteration.**  `agreePrefix` := the largest `t` with cache agreement on
`[0, t]`; the exchange increases it by ≥ 1; well-founded recursion on
`σ.length + 1 - agreePrefix` yields a schedule whose caches agree with
`F` on `[0, σ.length]`, so `misses F = misses (its policy schedule) ≤
misses π`.  (Equivalently: strong induction on the number of remaining
positions.)

## Third pass: counterexamples pin down the correct construction (2026-08-08)

**The "simple modification + follow d" schedule is NOT correct.**  Worked
counterexample: `σ = [p, x, q, q', q]`, `C₀ = {q, q', x}` (FIF evicts `q'`
at `t = 0`, `π` evicts `q`).  With `d'` evicting `q'` at 0 and following
`d` elsewhere (junk at hit positions chosen by `π`), if `d₃ = q` (π's junk
at the hit on `q'`) then `d'` evicts `q` at position 3 and faults again on
`q` at position 4, giving `misses d' = 3 > 2 = misses d`.  The junk values
of `d` at hit positions are arbitrary, so no "follow d" schedule is safe.
Fixing it by "evict the multi-set element" (`x`, which `d` evicted at
position 2 and `d'` kept) at position 3 keeps `q` in `d'`'s cache and the
exchange is cost-free.  Conclusion: the eviction at a "d hits, d' faults on
r ∈ {q,q'}" position must be an element of the multi-set
`C_s^{d'} \ C_s^d` (which is nonempty there by the size argument
`|multi| - |missing| = |C^{d'}| - |C^d| ≥ 0` and `q' ∈ missing`), which
makes `d'`'s decision depend on its own cache — a recursive (well-founded)
definition, or an existence-style construction via `Classical.choose`.

**Counterexample analysis also fixes the pairing.**  With the multi-set
choice: bad events are only `q'` at `v` (evicting `q` there; paired with
the good event at `u`) and `q` after a "`d` evicts `q'`" event (paired
with the `q'` request that must follow it, since `q'` was re-requested to
be evictable).  All other requests have equal fault statuses by the
invariant `∀ r ∉ {q,q'}, r ∈ C_s^{d'} ⟺ r ∈ C_s^d` (preserved by evicting
multi-set elements, `q`, `q'`, or `d s` — never a page `d` keeps that `d'`
lacks).  Hence `misses d' ≤ misses d`.

**Final decision logic for `exchangeSchedule` (verified by worked
examples, 2026-08-08).**  For `s > t`, with `C' := schedCache d' C₀ σ s`,
`C := schedCache d C₀ σ s`, `r := σ.getD s 0`, `M := C' \ C`:
1. `d s = q'` → evict `q`.
2. `r ∈ {q, q'}` and `r ∈ C` (d hits, d' will fault) → evict a multi-set
   element of `M` preferring `x ≠ q'` (at `v`: `M = {x}`-type, since
   `q ∈ C` there and `q' ∉ C'`; in the double-difference: prefer the
   `x`-type elements so `q'` stays and the `q'`-request good event
   survives).
3. otherwise (follow) → evict `d s` if `d s ∈ C'`, else a multi-set
   element if `M` is nonempty, else `0` (no-op).
The multi-set is never empty in the "d has q', d' lacks q'" states
(`|M| = |missing| ≥ 1` by the cache-size argument), so `q` is never
evicted while `d` keeps it: the bad event `q`-request-with-`d'`-missing
never occurs.  The only bad event is `q'` at `v` (evicting `q` there,
paired with the good event at `u`, since `u ≤ v`); all good events
(`u`, `q'` after each "d evicts q'" event, evicted-`x`-type requests)
dominate it.  Hence `misses d' ≤ misses d`.

**Open items for the implementation session:**
1. Recursive definition of `exchangeSchedule` (structural recursion on
   `s` with `schedCache` over its own prefix — verified feasible in Lean;
   multi-set choice via `Classical.choose` with the nonempty argument).
2. The invariant `∀ r ∉ {q,q'}, r ∈ C_s^{d'} ⟺ r ∈ C_s^d` (fault statuses
   equal off {q, q'}), the size argument `|M| ≥ |missing|`, and the
   bad-events ≤ good-events counting with the phase structure
   (`u` = next request of `q`, `v` = next request of `q'`, `u ≤ v` via
   `Farther`).
3. The iteration (agreement-prefix well-founded recursion) and the final
   bridge to `misses π`.
4. Estimated 600–900 remaining lines in `S3_Optimality.lean`; the
   schedule model (schedCache/policySchedule/bridges) is already
   implemented and committed (8e38fcd).

## Open design questions (superseded by the resolved design above; kept for history)

1. **The conjugate policy does NOT maintain the swap invariant — verified
   by hand (2026-08-08).**  `π'.evict i D r := conj(π.evict i (swap D) r)`
   applies `π` to `swap(C_s^{π'}) = swap(swap(C_s^π))`, which differs from
   `C_s^π` when `f ∈ C_s^π, e ∉ C_s^π` (the "f-only" config).  The invariant
   step then requires `π.evict s (C_s^π) r = π.evict s (swap(swap(C_s^π))) r`
   — false in general.  Applying `π` to `D` directly has the same problem
   (`C_s^{π'}` vs `C_s^π` differ).  Conclusion: no policy of the form
   "apply `π`'s eviction function to a cache derived from `D`" maintains
   `C_s^{π'} = swap(C_s^π)`.
   **Options for the next design iteration:**
   - (a) Weaker invariant + charging: track only
     `C_s^{π'} ⊇ C_s^π - {f}` (or the diff ⊆ {e,f} ∪ "eviction artifacts"),
     and show the miss comparison via a charging/potential argument over
     the compensating faults (the f-request `+1` vs the e-request `-1`,
     with `u ≤ v` from the FIF property).
   - (b) Switch the exchange lemma to a *schedule* formulation (a sequence
     of eviction decisions — "S' evicts the same pages as S"), where the
     eviction correspondence is available by construction; Lemma 1
     (reduced schedules) then bridges schedules and policies.  This is the
     classical presentation (KT §4.3, the Goldner worksheet), but requires
     a new schedule model on top of the policy model.
   - (c) Keep the simple modification (evict `q'` at `(t, C)` only) and
     prove `misses π' ≤ misses π` directly by comparing fault statuses
     position by position, with the case analysis on where the diff pages
     are requested (the phase structure: before `u` (next request of `e`)
     neither `e` nor `f` is requested and the diff stays ⊆ {e,f}; at `u`
     `π'` hits where `π` faults; after `u` the compensating `+1`s — the
     `{f}`-diff and `{f,x}`-diff chases — need a clean summation lemma).
     This avoids defining any conjugate policy but needs a careful
     per-position fault-status lemma over the phases.
2. If option (c): the eviction at `(t, C)` modification is the only policy
   change; the per-position lemma compares `faultAt π'` vs `faultAt π`
   using the diff set `D_s := C_s^π △ C_s^{π'}` and the phase partition of
   the request positions (before/at/after `u`, plus the "S evicts f"
   sub-case where the caches coincide).
3. Iteration termination: define `agreePrefix π` as the largest `t` with
   agreement; the exchange increases it by ≥ 1; recursion on
   `σ.length + 1 - agreePrefix`.
4. The initial-cache `C₀.Nonempty` hypothesis is needed by `Policy.evict_mem`
   (via `mem_farthestInFuture`); the run keeps caches nonempty
   (`cacheSeq_nonempty`).

## Suggested file layout

All in `S3_Optimality.lean`:
- `swapCache (e f) (C)`, `swapCache_f_of_mem`, `swapCache_f_not_mem`,
  `swapCache_idem_on` (or the specific set identities needed)
- `conjugatePolicy (π) (e f)` + `conjugate_evict_mem`
- `exchange (π) (t) (hagr) (hdiff) : ∃ π', misses π' ≤ misses π ∧
  cachesAgree π' (t+1)`
- `agreePrefix` / `firstDiff` + `fifo_optimal` via well-founded iteration
- module doc update + metadata (CSV, proof map, Progress.lean) as usual
