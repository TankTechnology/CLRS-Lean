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

## Open design questions (to settle before writing code)

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
