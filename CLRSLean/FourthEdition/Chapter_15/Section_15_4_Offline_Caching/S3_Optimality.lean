import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S1_Cache_Model
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S2_Farthest_In_Future

/-!
# S3. Optimality of the farthest-in-future policy

The exchange-schedule machinery for the optimality proof of the
farthest-in-future (Belady) eviction policy of CLRS §15.4, plus basic sanity
lemmas for the policy itself: it always evicts a resident page and preserves
the cache size.

Main results:

- `fifo_evicts_resident`: the FIF policy evicts a resident page
- `fifo_step_size`: a FIF step preserves the cache size
- `schedCache` / `schedMisses`: the run and miss count of an arbitrary
  eviction schedule; a policy's schedule incurs exactly the policy's misses
- `exchangeSchedule_invariant`: from the first disagreement `t` onwards, the
  exchange schedule's cache contains every page of `d`'s cache except
  possibly `q` and `q'`, so a fault where `d` hits can only be a request of
  `q` or `q'`
- `exchangeDecision_of_hit` / `exchangeDecision_of_fault`: the exchange
  eviction at a hit is `q`, `q'`, or a page `d`'s cache lacks; at a fault it
  is additionally `d s`
- `exchangeSchedule_misses_le`: one exchange step never increases the miss
  count — the good event at the first request of `q` compensates the unique
  bad event at the first request of `q'` (or `q'` is never requested again).
  The chain of supporting lemmas is proved under a *weakened* reducedness
  hypothesis `hweak : ∀ s, t ≤ s → fault of `d` at `s` → `d s` resident`,
  so the counting lemma applies to schedules that are reduced only from the
  exchange position on (the iteration's exchange schedules are reduced at
  every fault after the first `q'` request, by
  `exchangeSchedule_reduced_after`)
- `exchangeSchedule_q_mem` / `exchangeSchedule_q'_mem`: from the first `q`
  (resp. `q'`) request on, a page resident in `d`'s cache is also resident in
  the exchange cache, so bad events are confined to the first `q'` request
- `fifoSchedule`: the eviction schedule of the farthest-in-future policy
- `first_disagree`: at a first disagreement of a reduced schedule, both
  schedules fault, the evictions differ, and the policy's eviction is
  resident
- `exchange_step`: exchanging the first disagreement of a reduced schedule
  never increases misses and extends agreement with `fifoSchedule` by one
  position
- `exchangeSchedule_reduced_after`: the exchange schedule is reduced at every
  fault after the first `q'` request, so the reducedness state needed by the
  iteration is preserved from one exchange to the next
- `exchangeSchedule_misses_le_plus_one`: when the bad event did not occur
  (`q'` never requested again and `q` is, or `d` evicts `q'` before its first
  request), the exchange saves a spare miss — the compensating slack for the
  repair step
- `repairSchedule` / `repair_step`: replacing a no-op eviction at the first
  disagreement by the policy's choice (`q'`, evicted again at its first
  request so the caches coincide afterwards) costs at most one extra miss and
  extends agreement by one position, with the window up to `J'` relation
  `repairSchedule_window` and the post-`J'` containment
  `repairSchedule_superset`

Current gaps:

- The optimality theorem (`fifo_optimal`: no eviction policy — even offline —
  has fewer misses than the farthest-in-future policy, CLRS Theorem 15.5)
  remains to be formalized.  The iteration machinery is in place:
  `exchange_step` shows that exchanging the first disagreement of a schedule
  reduced from that position on never increases misses and extends agreement
  with the farthest-in-future policy by one position, and
  `exchangeSchedule_reduced_after` shows the reducedness state (reduced at
  every fault after a bound `hnb`) is preserved by the exchange (with the
  bound growing to `max hnb J'`).  The remaining work is the iteration
  assembly: repeatedly exchanging at the first disagreement while the
  schedule is reduced from there on produces a schedule agreeing with the
  policy everywhere with no more misses.  The pieces are in place —
  `exchange_step` (never increases misses, extends agreement), the slack
  lemma `exchangeSchedule_misses_le_plus_one` (spare miss when the bad event
  did not occur), and the repair step `repair_step` (replacing a no-op
  eviction at or before the reducedness bound by the policy's choice costs
  at most one extra miss, paid by the slack) — so the remaining work is the
  iteration state machine: tracking the reducedness bound, the previous
  `q'`/`J'` and the accumulated slack, choosing between the exchange and the
  repair at each first disagreement, and the boundary case where the first
  disagreement lands exactly on the previous `q'` request.
-/

namespace CLRS

namespace Caching

open Finset

/-- The farthest-in-future policy always evicts a resident page. -/
lemma fifo_evicts_resident (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page)
    (hp : p ∉ C) (hC : C.Nonempty) :
    (fifoPolicy σ).evict i C p ∈ C :=
  (fifoPolicy σ).evict_mem i C p hp hC

/-- A step of the farthest-in-future policy preserves the cache size. -/
lemma fifo_step_size (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page)
    (hC : C.Nonempty) :
    ((fifoPolicy σ).step i C p).card = C.card :=
  step_card (fifoPolicy σ) i C p hC

/--
A **schedule** for the request list `σ` is a decision function
`d : ℕ → Page` giving, for every position `s`, the page to evict at that
position.  The schedule's run `schedCache d C₀ σ` starts from `C₀`: a hit
keeps the cache, a fault evicts `d s` (an eviction of an absent page is a
no-op, so schedules need not be reduced) and loads the requested page.
-/
def schedCache (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) : ℕ → Finset Page
  | 0 => C₀
  | s + 1 => if σ.getD s 0 ∈ schedCache d C₀ σ s then schedCache d C₀ σ s
             else insert (σ.getD s 0) ((schedCache d C₀ σ s).erase (d s))

/-- Whether position `s` is a miss for the schedule `d` from `C₀` on `σ`
(`0` or `1`). -/
def schedFaultAt (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) (s : ℕ) : ℕ :=
  if σ.getD s 0 ∈ schedCache d C₀ σ s then 0 else 1

/-- The number of misses of the schedule `d` from `C₀` on `σ`. -/
def schedMisses (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) : ℕ :=
  ∑ s ∈ Finset.range σ.length, schedFaultAt d C₀ σ s

/-- The schedule induced by a policy: at position `s` it evicts exactly the
page the policy evicts in its own run. -/
def policySchedule (π : Policy) (C₀ : Finset Page) (σ : List Page) : ℕ → Page :=
  fun s => π.evict s (cacheSeq π C₀ σ s) (σ.getD s 0)

/-- The run of a policy's schedule is the policy's own run. -/
lemma schedCache_policySchedule (π : Policy) (C₀ : Finset Page) (σ : List Page) (s : ℕ) :
    schedCache (policySchedule π C₀ σ) C₀ σ s = cacheSeq π C₀ σ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      unfold schedCache
      rw [ih]
      cases s with
      | zero => rfl
      | succ s' =>
          unfold cacheSeq
          rfl

/-- A policy and its schedule incur the same number of misses. -/
lemma schedMisses_policySchedule (π : Policy) (C₀ : Finset Page) (σ : List Page) :
    schedMisses (policySchedule π C₀ σ) C₀ σ = misses π C₀ σ := by
  unfold schedMisses misses faultAt
  apply Finset.sum_congr rfl
  intro s hs
  unfold schedFaultAt
  rw [schedCache_policySchedule]

/--
The **exchange schedule** for the first fault where `d` and the
farthest-in-future policy disagree (position `t`, request `p`, `d` evicting
`q`, the policy evicting `q'`): it agrees with `d` before `t`, evicts `q'`
at `t`, and afterwards follows `d` except that it never evicts a page that
`d` keeps while the exchange schedule lacks it (when `d` evicts `q'` the
exchange schedule evicts `q'` too — a no-op when it already lacks `q'` —
and a multi-set element — a page `d` does not have — when `d` hits a
request of `q` or `q'` that the exchange schedule misses), so that no bad
event (a fault where `d` hits) is created.

The eviction decision at position `s`, based on the exchange schedule's
cache `C'` (the cache just before the request at `s`) and `d`'s cache. -/
noncomputable def exchangeDecision (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ C' : Finset Page) (s : ℕ) : Page :=
  if s < t then d s
  else if s = t then q'
  else if d s = q' then q'
  else if (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧ σ.getD s 0 ∈ schedCache d C₀ σ s then
    let M : Finset Page := C' \ schedCache d C₀ σ s
    if h : (M.filter (fun x => x ≠ q')).Nonempty then Classical.choose h
    else if h : M.Nonempty then Classical.choose h
    else 0
  else if d s ∈ C' then d s
  else
    let M : Finset Page := C' \ schedCache d C₀ σ s
    if h : M.Nonempty then Classical.choose h
    else 0

noncomputable def exchangeScheduleCore (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) : ℕ → Finset Page × Page
  | 0 => (C₀, exchangeDecision d t q q' σ C₀ C₀ 0)
  | s + 1 =>
      let prev := exchangeScheduleCore d t q q' σ C₀ s
      let r : Page := σ.getD s 0
      let Csucc : Finset Page :=
        if r ∈ prev.1 then prev.1 else insert r (prev.1.erase prev.2)
      (Csucc, exchangeDecision d t q q' σ C₀ Csucc (s + 1))

/-- The decision function of the exchange schedule. -/
noncomputable def exchangeSchedule (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) : ℕ → Page :=
  fun s => (exchangeScheduleCore d t q q' σ C₀ s).2

/-- The exchange schedule's run is the cache component of the core. -/
lemma schedCache_exchangeScheduleCore (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) (s : ℕ) :
    schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s =
      (exchangeScheduleCore d t q q' σ C₀ s).1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      unfold schedCache
      rw [ih]
      cases s with
      | zero => rfl
      | succ s' =>
          unfold exchangeScheduleCore
          rfl

/-- Strictly before `t`, the exchange schedule's cache and decision agree
with `d`'s. -/
lemma exchangeScheduleCore_eq_d (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) {s : ℕ} (hs : s < t) :
    exchangeScheduleCore d t q q' σ C₀ s = (schedCache d C₀ σ s, d s) := by
  induction s with
  | zero =>
      unfold exchangeScheduleCore
      simp [exchangeDecision, hs]
      rfl
  | succ s ih =>
      rw [exchangeScheduleCore]
      rw [ih (lt_trans (Nat.lt_succ_self s) hs)]
      simp [exchangeDecision, hs]
      cases s with
      | zero => rfl
      | succ s' =>
          unfold schedCache
          rfl

/-- The exchange schedule agrees with `d` strictly before `t`. -/
lemma exchangeSchedule_eq_d_of_lt (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) {s : ℕ} (hs : s < t) :
    exchangeSchedule d t q q' σ C₀ s = d s := by
  unfold exchangeSchedule
  rw [exchangeScheduleCore_eq_d d t q q' σ C₀ hs]

/-- Up to and including position `t`, the exchange schedule's cache agrees
with `d`'s. -/
lemma schedCache_exchangeSchedule_eq_d (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) {s : ℕ} (hs : s ≤ t) :
    schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s = schedCache d C₀ σ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      unfold schedCache
      rw [exchangeSchedule_eq_d_of_lt d t q q' σ C₀ (Nat.lt_of_succ_le hs)]
      rw [ih (by omega)]


/-- The exchange schedule evicts `q'` at position `t`. -/
lemma exchangeSchedule_at_t (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) :
    exchangeSchedule d t q q' σ C₀ t = q' := by
  unfold exchangeSchedule exchangeScheduleCore
  induction t with
  | zero => simp [exchangeDecision]
  | succ t ih =>
      unfold exchangeScheduleCore
      simp [exchangeDecision]

/-- A reduced schedule's cache size is constant (evictions hit resident
pages and faults load a page that was absent). -/
lemma schedCache_card_const (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page)
    (t : ℕ)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hts : t ≤ s) : (schedCache d C₀ σ (s + 1)).card = (schedCache d C₀ σ s).card := by
  rw [schedCache]
  by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
  · rw [if_pos hr]
  · rw [if_neg hr]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_erase_of_mem (hweak s hts hr)]
      have hc : 0 < (schedCache d C₀ σ s).card :=
        Finset.card_pos.mpr ⟨d s, hweak s hts hr⟩
      omega
    · intro hm
      exact hr (Finset.mem_erase.mp hm).2

/-- One step never shrinks the exchange schedule's cache. -/
lemma exchangeScheduleCore_card_step (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) (s : ℕ) :
    (exchangeScheduleCore d t q q' σ C₀ (s + 1)).1.card ≥
      (exchangeScheduleCore d t q q' σ C₀ s).1.card := by
  rw [exchangeScheduleCore]
  by_cases hr : σ.getD s 0 ∈ (exchangeScheduleCore d t q q' σ C₀ s).1
  · rw [if_pos hr]
  · rw [if_neg hr]
    rw [Finset.card_insert_of_notMem]
    · have hle : ((exchangeScheduleCore d t q q' σ C₀ s).1.erase
          (exchangeScheduleCore d t q q' σ C₀ s).2).card + 1 ≥
          (exchangeScheduleCore d t q q' σ C₀ s).1.card := by
        by_cases hx : (exchangeScheduleCore d t q q' σ C₀ s).2 ∈
          (exchangeScheduleCore d t q q' σ C₀ s).1
        · rw [Finset.card_erase_of_mem hx]
          omega
        · simp [hx]
      omega
    · intro hm
      exact hr (Finset.mem_erase.mp hm).2

/-- The exchange schedule's cache never shrinks below `d`'s: from `t`
onwards it has at least as many pages as `d`'s cache. -/
lemma exchangeScheduleCore_card (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hs : t ≤ s) :
    (exchangeScheduleCore d t q q' σ C₀ s).1.card ≥ (schedCache d C₀ σ s).card := by
  have hmono : (exchangeScheduleCore d t q q' σ C₀ s).1.card ≥
      (exchangeScheduleCore d t q q' σ C₀ t).1.card := by
    induction s with
    | zero =>
        have ht : t = 0 := by omega
        subst t
        rfl
    | succ s ih =>
        by_cases hst : t ≤ s
        · exact le_trans (ih hst) (exchangeScheduleCore_card_step d t q q' σ C₀ s)
        · have hs' : s + 1 = t := by omega
          rw [← schedCache_exchangeScheduleCore]
          rw [← schedCache_exchangeScheduleCore]
          rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ (le_of_eq hs')]
          rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
          rw [hs']
  have hbase : (exchangeScheduleCore d t q q' σ C₀ t).1.card = (schedCache d C₀ σ t).card := by
    rw [← schedCache_exchangeScheduleCore]
    rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
  have hconst : (schedCache d C₀ σ s).card = (schedCache d C₀ σ t).card := by
    have h : ∀ n, (schedCache d C₀ σ (t + n)).card = (schedCache d C₀ σ t).card := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Nat.add_succ]
          rw [schedCache_card_const d C₀ σ t hweak (s := t + n) (by omega)]
          exact ih
    have hs' : s = t + (s - t) := by omega
    rw [hs']
    exact h (s - t)
  rw [hconst]
  rw [← hbase]
  exact hmono

/-- The decision component of the core is the exchange decision at the same
position. -/
lemma exchangeScheduleCore_second (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page) (s : ℕ) :
    (exchangeScheduleCore d t q q' σ C₀ s).2 =
      exchangeDecision d t q q' σ C₀ (exchangeScheduleCore d t q q' σ C₀ s).1 s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [exchangeScheduleCore]

/-- When `d` hits at `s` and the exchange schedule faults, the exchange
eviction at `s` is `q`, `q'`, or a page `d`'s cache lacks. -/
lemma exchangeDecision_of_hit (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ C' : Finset Page) {s : ℕ} (hst : t < s)
    (hr : σ.getD s 0 ∈ schedCache d C₀ σ s) (hr' : σ.getD s 0 ∉ C')
    (hrqq : σ.getD s 0 = q' ∨ σ.getD s 0 = q)
    (hcard : (schedCache d C₀ σ s).card ≤ C'.card) :
    exchangeDecision d t q q' σ C₀ C' s = q ∨
      exchangeDecision d t q q' σ C₀ C' s = q' ∨
      exchangeDecision d t q q' σ C₀ C' s ∉ schedCache d C₀ σ s := by
  unfold exchangeDecision
  have hlt : ¬ s < t := by omega
  have hne : ¬ s = t := by omega
  rw [if_neg hlt, if_neg hne]
  by_cases h1 : d s = q'
  · rw [if_pos h1]
    exact Or.inr (Or.inl rfl)
  · rw [if_neg h1]
    by_cases h2 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
        σ.getD s 0 ∈ schedCache d C₀ σ s
    · rw [if_pos h2]
      by_cases hf : ((C' \ schedCache d C₀ σ s).filter (fun x => x ≠ q')).Nonempty
      · rw [dif_pos hf]
        right; right
        have hspec := Classical.choose_spec hf
        intro hdec
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hspec).1).2 hdec
      · rw [dif_neg hf]
        by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
        · rw [dif_pos hm]
          right; right
          have hspec := Classical.choose_spec hm
          intro hdec
          exact (Finset.mem_sdiff.mp hspec).2 hdec
        · rw [dif_neg hm]
          exfalso
          have hsub : C' ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hEq : C' = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          have hrC' : σ.getD s 0 ∈ C' := by
            rw [hEq]
            exact hr
          exact hr' hrC'
    · rw [if_neg h2]
      exfalso
      exact h2 ⟨hrqq, hr⟩

/-- When `d` faults at `s`, the exchange eviction at `s` is `q`, `q'`, `d s`,
or a page `d`'s cache lacks. -/
lemma exchangeDecision_of_fault (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ C' : Finset Page)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hst : t < s) (hr : σ.getD s 0 ∉ schedCache d C₀ σ s)
    (hcard : (schedCache d C₀ σ s).card ≤ C'.card) :
    exchangeDecision d t q q' σ C₀ C' s = q ∨
      exchangeDecision d t q q' σ C₀ C' s = q' ∨
      exchangeDecision d t q q' σ C₀ C' s = d s ∨
      exchangeDecision d t q q' σ C₀ C' s ∉ schedCache d C₀ σ s := by
  unfold exchangeDecision
  have hlt : ¬ s < t := by omega
  have hne : ¬ s = t := by omega
  rw [if_neg hlt, if_neg hne]
  by_cases h1 : d s = q'
  · rw [if_pos h1]
    exact Or.inr (Or.inl rfl)
  · rw [if_neg h1]
    by_cases h2 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
        σ.getD s 0 ∈ schedCache d C₀ σ s
    · exfalso
      exact hr h2.2
    · rw [if_neg h2]
      by_cases h3 : d s ∈ C'
      · rw [if_pos h3]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [if_neg h3]
        by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
        · rw [dif_pos hm]
          right; right; right
          have hspec := Classical.choose_spec hm
          intro hdec
          exact (Finset.mem_sdiff.mp hspec).2 hdec
        · rw [dif_neg hm]
          exfalso
          have hsub : C' ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hEq : C' = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          have hds : d s ∈ C' := by
            rw [hEq]
            exact hweak s (by omega) hr
          exact h3 hds


/--
The **invariant of the exchange schedule**: for every position `s ≥ t+1`,
the exchange schedule's cache contains every page of `d`'s cache except
possibly `q` and `q'`.  Consequently a fault of `d` on a request outside
`{q, q'}` is never a hit of the exchange schedule — bad events (faults
where `d` hits) can only happen on requests of `q` or `q'`.
-/
lemma exchangeSchedule_invariant (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s) :
    ∀ s ≥ t + 1, ∀ x, x ∉ ({q, q'} : Finset Page) →
      x ∈ schedCache d C₀ σ s →
      x ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  intro s hs
  induction s with
  | zero => omega
  | succ s ih =>
      intro x hx hmem
      by_cases hst : s = t
      · -- base: after the request at t, the caches differ only in q vs q'
        subst s
        rw [schedCache_exchangeScheduleCore]
        rw [exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).1 = schedCache d C₀ σ t by
          rw [← schedCache_exchangeScheduleCore]
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).2 = q' by
          exact exchangeSchedule_at_t d t q q' σ C₀]
        unfold schedCache at hmem
        rw [hq] at hmem
        by_cases hp : σ.getD t 0 ∈ schedCache d C₀ σ t
        · rw [if_pos hp] at hmem ⊢
          exact hmem
        · rw [if_neg hp] at hmem ⊢
          rcases Finset.mem_insert.mp hmem with hxeq | hxin
          · rw [hxeq]
            exact Finset.mem_insert_self (σ.getD t 0) ((schedCache d C₀ σ t).erase q')
          · have hxq' : x ≠ q' := by
              intro h
              exact hx (by simp [h])
            exact Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hxq', (Finset.mem_erase.mp hxin).2⟩)
      · -- step: s > t
        have hs' : t + 1 ≤ s := by omega
        have hst : t < s := by omega
        have ih' := ih hs'
        rw [schedCache_exchangeScheduleCore]
        rw [exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).1 =
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s by
          rw [← schedCache_exchangeScheduleCore]]
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).2 = exchangeDecision d t q q' σ C₀
            (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s by
          rw [exchangeScheduleCore_second]
          congr 1
          rw [← schedCache_exchangeScheduleCore]]
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · -- d hits at s
          unfold schedCache at hmem
          rw [if_pos hr] at hmem
          by_cases hr' : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
          · -- the exchange schedule hits too: no eviction
            rw [if_pos hr']
            exact ih' x hx hmem
          · -- d hits, the exchange schedule faults: the decision evicts q, q',
            -- or a page d's cache lacks, so x survives
            rw [if_neg hr']
            have hrqq : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
              by_contra hnot
              exact hr' (ih' (σ.getD s 0) (by
                intro hmem
                apply hnot
                rcases Finset.mem_insert.mp hmem with hqeq | hq'
                · exact Or.inr hqeq
                · exact Or.inl (Finset.mem_singleton.mp hq')) hr)
            have hcard : (schedCache d C₀ σ s).card ≤
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).card := by
              rw [schedCache_exchangeScheduleCore]
              exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
            have hdec := exchangeDecision_of_hit d t q q' σ C₀
              (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) hst hr hr' hrqq hcard
            have hxq : x ≠ q := by
              intro h
              exact hx (by simp [h])
            have hxq' : x ≠ q' := by
              intro h
              exact hx (by simp [h])
            have hxne : x ≠ exchangeDecision d t q q' σ C₀
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s := by
              intro hxdec
              rcases hdec with hdecq | hdecq' | hdecnot
              · exact hxq (hxdec.trans hdecq)
              · exact hxq' (hxdec.trans hdecq')
              · exact hdecnot (hxdec ▸ hmem)
            have hxC' : x ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
              ih' x hx hmem
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxne, hxC'⟩)
        · -- d faults at s
          unfold schedCache at hmem
          rw [if_neg hr] at hmem
          by_cases hr' : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
          · -- the exchange schedule hits: its cache is unchanged
            rw [if_pos hr']
            rcases Finset.mem_insert.mp hmem with hxr | hxin
            · rw [hxr]
              exact hr'
            · exact ih' x hx (Finset.mem_erase.mp hxin).2
          · -- both fault: r is inserted, and the decision evicts q, q', d s, or
            -- a page d's cache lacks, so x survives
            rw [if_neg hr']
            rcases Finset.mem_insert.mp hmem with hxr | hxin
            · rw [hxr]
              exact Finset.mem_insert_self (σ.getD s 0) _
            · have hxC_d : x ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hxin).2
              have hxne_ds : x ≠ d s := (Finset.mem_erase.mp hxin).1
              have hcard : (schedCache d C₀ σ s).card ≤
                  (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).card := by
                rw [schedCache_exchangeScheduleCore]
                exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
              have hdec := exchangeDecision_of_fault d t q q' σ C₀
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) hweak hst hr hcard
              have hxq : x ≠ q := by
                intro h
                exact hx (by simp [h])
              have hxq' : x ≠ q' := by
                intro h
                exact hx (by simp [h])
              have hxne : x ≠ exchangeDecision d t q q' σ C₀
                  (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s := by
                intro hxdec
                rcases hdec with hdecq | hdecq' | hdecds | hdecnot
                · exact hxq (hxdec.trans hdecq)
                · exact hxq' (hxdec.trans hdecq')
                · exact hxne_ds (hxdec.trans hdecds)
                · exact hdecnot (hxdec ▸ hxC_d)
              have hxC' : x ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
                ih' x hx hxC_d
              exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxne, hxC'⟩)


/-- If `q'` is the farthest-in-future page of a cache at position `i` and
`q` is a different resident page, then either `q'` is never requested
again, or `q`'s next request comes strictly before `q'`'s next request. -/
lemma fifo_nextUse_order (σ : List Page) (cache : Finset Page) (i : ℕ) (q' q : Page)
    (hq' : q' = farthestInFuture cache σ i) (hq : q ∈ cache) (hqq' : q ≠ q') :
    nextUse σ (i + 1) q' = none ∨
      ∃ j j', nextUse σ (i + 1) q = some j ∧ nextUse σ (i + 1) q' = some j' ∧ j < j' := by
  have hmax := farthestInFuture_max (σ := σ) (i := i) (p := q) hq
  rw [← hq'] at hmax
  have hc := farther_cases hmax
  rcases hc with hnone' | ⟨jq', jq, hq'eq, hqeq, hle⟩
  · exact Or.inl hnone'
  · right
    refine ⟨jq, jq', hqeq, hq'eq, ?_⟩
    have hne : jq ≠ jq' := by
      intro hjj
      have hget := getD_eq_nextUse hqeq
      have hget' := getD_eq_nextUse hq'eq
      rw [hjj] at hget
      exact hqq' (hget.symm.trans hget')
    omega

/-- 在第一个 q 请求之前(含),`d` 的 cache 不含 `q`(`d` 在 `t` 逐出 `q`,且
`q` 在 `(t, J)` 内未被请求)。 -/
lemma d_cache_ne_q (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    {s : ℕ} (hs1 : t < s) (hs2 : s ≤ t + 1 + j) :
    q ∉ schedCache d C₀ σ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t
      · subst s
        rw [schedCache, hq, if_neg hft]
        rw [Finset.mem_insert]
        intro h
        rcases h with hqr | hqin
        · have hqinD : q ∈ schedCache d C₀ σ t := by
            have hd : d t ∈ schedCache d C₀ σ t := hweak t le_rfl hft
            rw [hq] at hd
            exact hd
          exact hft (hqr ▸ hqinD)
        · exact (by simpa [hq] using (Finset.mem_erase.mp hqin).1)
      · have hts : t < s := by omega
        have hsJ : s < t + 1 + j := by omega
        rw [schedCache]
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · rw [if_pos hr]
          exact ih hts (by omega)
        · rw [if_neg hr]
          intro hmem
          rcases Finset.mem_insert.mp hmem with hqr | hqin
          · have hneq := getD_ne_nextUse hj (by omega) hsJ
            exact hneq hqr.symm
          · exact ih hts (by omega) (Finset.mem_erase.mp hqin).2

/-- 在第一个 q 请求之前,交换的 cache 与 d 的 cache 只差 q' 与 q 的交换。 -/
lemma exchangeSchedule_window (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q)
    (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q')
    {s : ℕ} (hs1 : t < s) (hs2 : s ≤ t + 1 + j) :
    schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s =
      insert q ((schedCache d C₀ σ s).erase q') := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t
      · subst s
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).1 = schedCache d C₀ σ t by
          rw [← schedCache_exchangeScheduleCore]
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).2 = q' by
          exact exchangeSchedule_at_t d t q q' σ C₀]
        rw [if_neg hft]
        rw [schedCache]
        rw [hq]
        rw [if_neg hft]
        -- 目标:insert r (D(t) − q') = insert q ((insert r (D(t) − q)) − q')
        have hqin : q ∈ schedCache d C₀ σ t := by
          have hd : d t ∈ schedCache d C₀ σ t := hweak t le_rfl hft
          rw [hq] at hd
          exact hd
        have hr_ne_q : σ.getD t 0 ≠ q := by
          intro h
          exact hft (h ▸ hqin)
        have hr_ne_q' : σ.getD t 0 ≠ q' := by
          intro h
          exact hft (h ▸ hq'res)
        apply Finset.ext
        intro x
        constructor
        · intro hx
          rw [Finset.mem_insert]
          rcases Finset.mem_insert.mp hx with hxr | hxin
          · subst x
            right
            rw [Finset.mem_erase]
            constructor
            · exact hr_ne_q'
            · rw [Finset.mem_insert]
              left
              rfl
          · by_cases hxq : x = q
            · left
              exact hxq
            · right
              rw [Finset.mem_erase]
              constructor
              · exact (Finset.mem_erase.mp hxin).1
              · rw [Finset.mem_insert]
                right
                exact Finset.mem_erase.mpr ⟨hxq, (Finset.mem_erase.mp hxin).2⟩
        · intro hx
          rw [Finset.mem_insert] at hx
          rcases hx with hxq | hxin
          · subst x
            rw [Finset.mem_insert]
            right
            rw [Finset.mem_erase]
            constructor
            · exact hqq'
            · exact hqin
          · have hxne_q' : x ≠ q' := (Finset.mem_erase.mp hxin).1
            rw [Finset.mem_insert]
            rcases Finset.mem_insert.mp (Finset.mem_erase.mp hxin).2 with hxr | hxin2
            · left
              exact hxr
            · right
              rw [Finset.mem_erase]
              constructor
              · exact hxne_q'
              · exact (Finset.mem_erase.mp hxin2).2
      · -- 步进:t < s,处理位置 s
        have hts : t < s := by omega
        have hsJ : s < t + 1 + j := by omega
        have hqne : q ∉ schedCache d C₀ σ s :=
          d_cache_ne_q d t q q' σ C₀ hq hweak hft hj hts (by omega)
        have hsig_ne_q : σ.getD s 0 ≠ q := getD_ne_nextUse hj (by omega) hsJ
        have hsig_ne_q' : σ.getD s 0 ≠ q' := hq'ne s (by omega) hsJ
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).1 =
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s by
          rw [← schedCache_exchangeScheduleCore]]
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).2 = exchangeDecision d t q q' σ C₀
            (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s by
          rw [exchangeScheduleCore_second]
          congr 1
          rw [← schedCache_exchangeScheduleCore]]
        rw [schedCache]
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · -- 双 hit
          rw [if_pos hr]
          have hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
            rw [ih hts (by omega)]
            rw [Finset.mem_insert]
            right
            rw [Finset.mem_erase]
            constructor
            · exact hsig_ne_q'
            · exact hr
          rw [if_pos hrE]
          rw [ih hts (by omega)]
        · -- 双 fault
          rw [if_neg hr]
          have hrE : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
            rw [ih hts (by omega)]
            intro hm
            rcases Finset.mem_insert.mp hm with hqeq | hmem
            · exact hsig_ne_q hqeq
            · exact hr (Finset.mem_erase.mp hmem).2
          rw [if_neg hrE]
          have hw := ih hts (by omega)
          rw [hw]
          unfold exchangeDecision
          have hlt : ¬ s < t := by omega
          have hne : ¬ s = t := by omega
          rw [if_neg hlt, if_neg hne]
          by_cases hdsq' : d s = q'
          · rw [if_pos hdsq']
            rw [hdsq']
            -- 两侧的 erase q' 都无效果
            have hq'notE : q' ∉ insert q ((schedCache d C₀ σ s).erase q') := by
              rw [Finset.mem_insert]
              intro hmem
              rcases hmem with hq'q | hq'mem
              · exact hqq' hq'q.symm
              · exact (Finset.mem_erase.mp hq'mem).1 rfl
            have hq'notE2 : q' ∉ insert (σ.getD s 0) ((schedCache d C₀ σ s).erase q') := by
              rw [Finset.mem_insert]
              intro hmem
              rcases hmem with hq'q | hq'mem
              · exact hsig_ne_q' hq'q.symm
              · exact (Finset.mem_erase.mp hq'mem).1 rfl
            rw [Finset.erase_eq_of_notMem hq'notE]
            rw [Finset.erase_eq_of_notMem hq'notE2]
            -- 两侧都等于 insert q (insert r (D(s) − q'))
            rw [Finset.insert_comm]
          · rw [if_neg hdsq']
            -- d s ≠ q':branch 4 不触发(σ[s] ∉ {q, q'})
            by_cases hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
                σ.getD s 0 ∈ schedCache d C₀ σ s
            · exfalso
              exact hb4.1.elim (fun h => hsig_ne_q' h) (fun h => hsig_ne_q h)
            · rw [if_neg hb4]
              -- d s ∈ E(s):由不变式(d s ∈ D(s) 且 d s ∉ {q, q'})
              have hdne : d s ≠ q := by
                intro hdsq
                exact hqne (hdsq ▸ hweak s (by omega) hr)
              have hdE : d s ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
                have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
                exact hinv (d s) (by
                  rw [Finset.mem_insert]
                  intro hmem
                  rcases hmem with hdsq | hdsqmem
                  · exact hdne hdsq
                  · exact hdsq' (Finset.mem_singleton.mp hdsqmem)) (hweak s (by omega) hr)
              have hdE' : d s ∈ insert q ((schedCache d C₀ σ s).erase q') := by
                rw [← hw]
                exact hdE
              rw [if_pos hdE']
              -- dec = d s :两侧都是 insert q (insert r (D(s) − {q', d s}))
              rw [Finset.erase_insert_of_ne hdne.symm]
              rw [Finset.erase_insert_of_ne hsig_ne_q']
              have herase_comm : ((schedCache d C₀ σ s).erase q').erase (d s) =
                  ((schedCache d C₀ σ s).erase (d s)).erase q' := by
                ext x
                simp [Finset.mem_erase, and_left_comm, and_assoc]
              rw [herase_comm]
              rw [Finset.insert_comm]

/-- 当 `p` 同时在 `d` 的 cache 和交换 cache 中时,交换在 `s` 的逐出不是
`p`(除非 `p` 是 `q'` 且 `d` 正好逐出 `q'`,这由 `hpq'` 排除;0 回退分支由
`h0hit`/`h0fault` 结合基数论证排除)。 -/
lemma exchangeDecision_ne (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hst : t < s) (C' : Finset Page) (p : Page)
    (hpE : p ∈ C') (hpD : p ∈ schedCache d C₀ σ s) (hdsq' : d s = q' → p ≠ q')
    (hdsC' : d s ∈ C' → p ≠ d s)
    (hcard : (schedCache d C₀ σ s).card ≤ C'.card)
    (h0hit : σ.getD s 0 ∈ schedCache d C₀ σ s → σ.getD s 0 ∉ C') :
    exchangeDecision d t q q' σ C₀ C' s ≠ p := by
  unfold exchangeDecision
  have hlt : ¬ s < t := by omega
  have hne : ¬ s = t := by omega
  rw [if_neg hlt, if_neg hne]
  by_cases h1 : d s = q'
  · rw [if_pos h1]
    intro hpeq
    exact hdsq' h1 hpeq.symm
  · rw [if_neg h1]
    by_cases h2 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
        σ.getD s 0 ∈ schedCache d C₀ σ s
    · rw [if_pos h2]
      by_cases hf : ((C' \ schedCache d C₀ σ s).filter (fun x => x ≠ q')).Nonempty
      · rw [dif_pos hf]
        intro hpeq
        have hspec := Classical.choose_spec hf
        have hpnotM : p ∉ C' \ schedCache d C₀ σ s := by
          intro hmem
          exact (Finset.mem_sdiff.mp hmem).2 hpD
        exact hpnotM (hpeq ▸ (Finset.mem_filter.mp hspec).1)
      · rw [dif_neg hf]
        by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
        · rw [dif_pos hm]
          intro hpeq
          have hspec := Classical.choose_spec hm
          have hpnotM : p ∉ C' \ schedCache d C₀ σ s := by
            rw [Finset.mem_sdiff]
            intro hmem
            exact hmem.2 hpD
          exact hpnotM (hpeq ▸ hspec)
        · rw [dif_neg hm]
          have hsub : C' ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hEq : C' = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          intro hpeq
          exact (h0hit h2.2) (hEq ▸ h2.2)
    · rw [if_neg h2]
      by_cases h3 : d s ∈ C'
      · rw [if_pos h3]
        intro hpeq
        exact hdsC' h3 hpeq.symm
      · rw [if_neg h3]
        by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
        · rw [dif_pos hm]
          intro hpeq
          have hspec := Classical.choose_spec hm
          have hpnotM : p ∉ C' \ schedCache d C₀ σ s := by
            rw [Finset.mem_sdiff]
            intro hmem
            exact hmem.2 hpD
          exact hpnotM (hpeq ▸ hspec)
        · rw [dif_neg hm]
          have hsub : C' ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hEq : C' = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          intro hpeq
          by_cases hr0 : σ.getD s 0 ∈ schedCache d C₀ σ s
          · exact (h0hit hr0) (hEq ▸ hr0)
          · have hdsin : d s ∈ C' := by
              rw [hEq]
              exact hweak s (by omega) hr0
            exact h3 hdsin

/-- 当 `σ[s] ∈ {q,q'}` 且 `d` 命中,而 `p` 同时在两个 cache 中时(branch 4
触发),交换在 `s` 的逐出不是 `p`。 -/
lemma exchangeDecision_ne_of_branch4 (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    {s : ℕ} (hst : t < s) (C' : Finset Page) (p : Page)
    (hpE : p ∈ C') (hpD : p ∈ schedCache d C₀ σ s) (hpq' : p ≠ q')
    (hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
      σ.getD s 0 ∈ schedCache d C₀ σ s)
    (hcard : (schedCache d C₀ σ s).card ≤ C'.card)
    (h0hit : σ.getD s 0 ∈ schedCache d C₀ σ s → σ.getD s 0 ∉ C') :
    exchangeDecision d t q q' σ C₀ C' s ≠ p := by
  unfold exchangeDecision
  have hlt : ¬ s < t := by omega
  have hne : ¬ s = t := by omega
  rw [if_neg hlt, if_neg hne]
  by_cases h1 : d s = q'
  · rw [if_pos h1]
    intro hpeq
    exact hpq' hpeq.symm
  · rw [if_neg h1]
    rw [if_pos hb4]
    by_cases hf : ((C' \ schedCache d C₀ σ s).filter (fun x => x ≠ q')).Nonempty
    · rw [dif_pos hf]
      intro hpeq
      have hspec := Classical.choose_spec hf
      have hpnotM : p ∉ C' \ schedCache d C₀ σ s := by
        intro hmem
        exact (Finset.mem_sdiff.mp hmem).2 hpD
      exact hpnotM (hpeq ▸ (Finset.mem_filter.mp hspec).1)
    · rw [dif_neg hf]
      by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
      · rw [dif_pos hm]
        intro hpeq
        have hspec := Classical.choose_spec hm
        have hpnotM : p ∉ C' \ schedCache d C₀ σ s := by
          intro hmem
          exact (Finset.mem_sdiff.mp hmem).2 hpD
        exact hpnotM (hpeq ▸ hspec)
      · rw [dif_neg hm]
        have hsub : C' ⊆ schedCache d C₀ σ s := by
          intro y hy
          by_contra hyn
          exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
        have hEq : C' = schedCache d C₀ σ s :=
          Finset.eq_of_subset_of_card_le hsub hcard
        intro hpeq
        exact (h0hit hb4.2) (hEq ▸ hb4.2)

/-- `q` 在 `d` 的 cache 中 ⟹ `q` 也在交换 cache 中(从 `t` 之后任意位置):
`q` 只会在 `d` 逐出它时离开交换 cache,而那时 `d` 也逐出它。 -/
lemma exchangeSchedule_q_mem (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q') :
    ∀ s, t < s → q ∈ schedCache d C₀ σ s →
      q ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs hqin
      by_cases hs_eq : s = t
      · -- q ∉ D(t+1):d 在 t 逐出 q,且 t 之前无 q 请求
        subst s
        exfalso
        have hqne : q ∉ schedCache d C₀ σ (t + 1) :=
          d_cache_ne_q d t q q' σ C₀ hq hweak hft hj (by omega) (by omega)
        exact hqne hqin
      · have hts : t < s := by omega
        -- 展开 E(s+1)
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).1 =
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s by
          rw [← schedCache_exchangeScheduleCore]]
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).2 = exchangeDecision d t q q' σ C₀
            (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s by
          rw [exchangeScheduleCore_second]
          congr 1
          rw [← schedCache_exchangeScheduleCore]]
        -- 展开 D(s+1) 于 hqin
        rw [schedCache] at hqin
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · -- d 命中:D(s+1) = D(s)
          rw [if_pos hr] at hqin
          have hqE : q ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
            ih hts hqin
          by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
          · rw [if_pos hrE]
            exact hqE
          · -- 坏事件:σ[s] ∈ D(s) − E(s) ⊆ {q, q'}
            rw [if_neg hrE]
            have hqqq' : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
              by_contra hnot
              have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
              exact hrE (hinv (σ.getD s 0) (by
                intro hmem
                apply hnot
                rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
                · exact Or.inr hqeq
                · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hr)
            rcases hqqq' with hq'eq | hqeq
            · -- σ[s] = q':branch 4 触发,dec ≠ q
              have hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
                  σ.getD s 0 ∈ schedCache d C₀ σ s := ⟨Or.inl hq'eq, hr⟩
              have hcard : (schedCache d C₀ σ s).card ≤
                  (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).card := by
                rw [schedCache_exchangeScheduleCore]
                exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
              have hdec : exchangeDecision d t q q' σ C₀
                  (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s ≠ q := by
                apply exchangeDecision_ne_of_branch4 d t q q' σ C₀ hqq' hweak hts
                · exact hqE
                · exact hqin
                · exact hqq'
                · exact hb4
                · exact hcard
                · exact fun _ => hrE
              exact Finset.mem_insert_of_mem (b := σ.getD s 0) (Finset.mem_erase.mpr ⟨hdec.symm, hqE⟩)
            · -- σ[s] = q:与 q ∈ E(s) 矛盾
              exfalso
              exact hrE (hqeq ▸ hqE)
        · -- d 错过
          rw [if_neg hr] at hqin
          rcases Finset.mem_insert.mp hqin with hqeq | hqin'
          · -- q = σ[s]:交换加载 q
            by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
            · rw [if_pos hrE]
              exact hqeq.symm ▸ hrE
            · rw [if_neg hrE]
              exact hqeq.symm ▸ Finset.mem_insert_self (σ.getD s 0) _
          · -- q ∈ D(s) 且 q ≠ d s
            have hqD : q ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hqin').2
            have hqds : q ≠ d s := (Finset.mem_erase.mp hqin').1
            have hqE : q ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
              ih hts hqD
            have hcard : (schedCache d C₀ σ s).card ≤
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).card := by
              rw [schedCache_exchangeScheduleCore]
              exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
            have hdec : exchangeDecision d t q q' σ C₀
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s ≠ q := by
              apply exchangeDecision_ne d t q q' σ C₀ hweak hts
              · exact hqE
              · exact hqD
              · intro hds
                exact hqq'
              · intro hdsin
                exact hqds
              · exact hcard
              · intro hmem
                exact False.elim (hr hmem)
            by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
            · rw [if_pos hrE]
              exact hqE
            · rw [if_neg hrE]
              exact Finset.mem_insert_of_mem (b := σ.getD s 0) (Finset.mem_erase.mpr ⟨hdec.symm, hqE⟩)

/-- 在第一个 `q'` 请求之前(含),交换 cache 不含 `q'`(`q'` 在 `t` 被逐出,
且 `(t, J')` 内无 `q'` 请求)。 -/
lemma exchangeSchedule_q'_absent (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    {s : ℕ} (hs1 : t < s) (hs2 : s ≤ t + 1 + j') :
    q' ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t
      · subst s
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).1 = schedCache d C₀ σ t by
          rw [← schedCache_exchangeScheduleCore]
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).2 = q' by
          exact exchangeSchedule_at_t d t q q' σ C₀]
        rw [if_neg hft]
        rw [Finset.mem_insert]
        intro hmem
        rcases hmem with hq'eq | hq'mem
        · exact hft (hq'eq ▸ hq'res)
        · exact (Finset.mem_erase.mp hq'mem).1 rfl
      · have hts : t < s := by omega
        have hsJ' : s < t + 1 + j' := by omega
        have hsig_ne_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse hj' (by omega) hsJ'
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).1 =
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s by
          rw [← schedCache_exchangeScheduleCore]]
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).2 = exchangeDecision d t q q' σ C₀
            (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s by
          rw [exchangeScheduleCore_second]
          congr 1
          rw [← schedCache_exchangeScheduleCore]]
        by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
        · rw [if_pos hrE]
          exact ih hts (by omega)
        · rw [if_neg hrE]
          intro hmem
          rcases Finset.mem_insert.mp hmem with hq'eq | hq'in
          · exact hsig_ne_q' hq'eq.symm
          · exact ih hts (by omega) (Finset.mem_erase.mp hq'in).2

/-- 从第一个 `q'` 请求之后,`q'` 在 `d` 的 cache 中 ⟹ `q'` 也在交换 cache
中(`q'` 在 `J'` 处被两个调度重新加载,之后只会随 `d` 一起逐出)。 -/
lemma exchangeSchedule_q'_mem (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q')
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j') :
    ∀ s, t + 1 + j' < s → q' ∈ schedCache d C₀ σ s →
      q' ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  intro s
  induction s with
  | zero => omega
  | succ s ih =>
      intro hs hqin
      by_cases hs_eq : s = t + 1 + j'
      · -- 基础:位置 J' 处交换加载 q'
        subst s
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ (t + 1 + j')).1 =
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1 + j') by
          rw [← schedCache_exchangeScheduleCore]]
        have hsig : σ.getD (t + 1 + j') 0 = q' := getD_eq_nextUse hj'
        have hJ'ne : σ.getD (t + 1 + j') 0 ∉
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1 + j') := by
          rw [hsig]
          apply exchangeSchedule_q'_absent d t q q' σ C₀ hweak hft hq'res hj'
          · omega
          · rfl
        rw [hsig]
        rw [hsig] at hJ'ne
        rw [if_neg hJ'ne]
        exact Finset.mem_insert_self q' _
      · have hsJ' : t + 1 + j' < s := by omega
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).1 =
            schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s by
          rw [← schedCache_exchangeScheduleCore]]
        rw [show (exchangeScheduleCore d t q q' σ C₀ s).2 = exchangeDecision d t q q' σ C₀
            (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s by
          rw [exchangeScheduleCore_second]
          congr 1
          rw [← schedCache_exchangeScheduleCore]]
        rw [schedCache] at hqin
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · -- d 命中
          rw [if_pos hr] at hqin
          have hq'E : q' ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
            ih hsJ' hqin
          by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
          · rw [if_pos hrE]
            exact hq'E
          · -- 坏事件:σ[s] ∈ D(s) − E(s) ⊆ {q, q'},两子情况都被成员引理排除
            rw [if_neg hrE]
            have hqqq' : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
              by_contra hnot
              have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
              exact hrE (hinv (σ.getD s 0) (by
                intro hmem
                apply hnot
                rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
                · exact Or.inr hqeq
                · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hr)
            rcases hqqq' with hq'eq | hqeq
            · exfalso
              exact hrE (hq'eq ▸ hq'E)
            · exfalso
              have hqE : q ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
                exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'ne s (by omega) (hqeq ▸ hr)
              exact hrE (hqeq ▸ hqE)
        · -- d 错过
          rw [if_neg hr] at hqin
          rcases Finset.mem_insert.mp hqin with hq'eq | hq'in
          · -- q' = σ[s]:交换加载 q'
            by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
            · rw [if_pos hrE]
              exact hq'eq.symm ▸ hrE
            · rw [if_neg hrE]
              exact hq'eq.symm ▸ Finset.mem_insert_self (σ.getD s 0) _
          · -- q' ∈ D(s) 且 q' ≠ d s
            have hts : t < s := by omega
            have hq'D : q' ∈ schedCache d C₀ σ s := (Finset.mem_erase.mp hq'in).2
            have hq'ds : q' ≠ d s := (Finset.mem_erase.mp hq'in).1
            have hq'E : q' ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s :=
              ih hsJ' hq'D
            have hcard : (schedCache d C₀ σ s).card ≤
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s).card := by
              rw [schedCache_exchangeScheduleCore]
              exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
            have hdec : exchangeDecision d t q q' σ C₀
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) s ≠ q' := by
              apply exchangeDecision_ne d t q q' σ C₀ hweak hts
              · exact hq'E
              · exact hq'D
              · intro hds
                exact False.elim (hq'ds hds.symm)
              · intro hdsin
                exact hq'ds
              · exact hcard
              · intro hmem
                exact False.elim (hr hmem)
            by_cases hrE : σ.getD s 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
            · rw [if_pos hrE]
              exact hq'E
            · rw [if_neg hrE]
              exact Finset.mem_insert_of_mem (b := σ.getD s 0) (Finset.mem_erase.mpr ⟨hdec.symm, hq'E⟩)

/-- 好事件:在第一个 `q` 请求处,交换命中而 `d` 错过。 -/
lemma exchangeSchedule_good (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q') :
    σ.getD (t + 1 + j) 0 ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1 + j) ∧
    σ.getD (t + 1 + j) 0 ∉ schedCache d C₀ σ (t + 1 + j) := by
  have hsig : σ.getD (t + 1 + j) 0 = q := getD_eq_nextUse hj
  constructor
  · rw [hsig]
    rw [exchangeSchedule_window d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'ne
      (s := t + 1 + j) (by omega) (by rfl)]
    rw [Finset.mem_insert]
    left
    rfl
  · rw [hsig]
    exact d_cache_ne_q d t q q' σ C₀ hq hweak hft hj (by omega) (by omega)

/-- 坏事件(交换错过而 `d` 命中)只可能发生在第一个 `q'` 请求处。 -/
lemma exchangeSchedule_bad (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q')
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    {s : ℕ} (hst : t < s) :
    σ.getD s 0 ∈ schedCache d C₀ σ s →
    σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s →
    s = t + 1 + j' := by
  intro hmem hnot
  have hqqq' : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
    by_contra hnot'
    have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
    exact hnot (hinv (σ.getD s 0) (by
      intro hmem2
      apply hnot'
      rcases Finset.mem_insert.mp hmem2 with hqeq | hq'eq
      · exact Or.inr hqeq
      · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hmem)
  rcases hqqq' with hq'eq | hqeq
  · -- σ[s] = q':排除 s < J' 和 s > J'
    by_cases hlt : s < t + 1 + j'
    · exfalso
      exact (getD_ne_nextUse hj' (by omega) hlt) hq'eq
    · by_cases hgt : t + 1 + j' < s
      · exfalso
        have hq'E : q' ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
          have hq'in' : q' ∈ schedCache d C₀ σ s := hq'eq ▸ hmem
          exact exchangeSchedule_q'_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'ne hj'
            s hgt hq'in'
        exact hnot (hq'eq ▸ hq'E)
      · omega
  · -- σ[s] = q:与 L-q 矛盾
    exfalso
    have hqE : q ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
      have hqin' : q ∈ schedCache d C₀ σ s := hqeq ▸ hmem
      exact exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'ne s hst hqin'
    exact hnot (hqeq ▸ hqE)

/-- 交换调度不比 `d` 多错过:好事件(首个 `q` 请求)补偿唯一的坏事件
(首个 `q'` 请求)。 -/
lemma exchangeSchedule_misses_le (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hfifo : nextUse σ (t + 1) q' = none ∨
      ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j') :
    schedMisses (exchangeSchedule d t q q' σ C₀) C₀ σ ≤ schedMisses d C₀ σ := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  let eF : ℕ → ℕ := schedFaultAt e C₀ σ
  let dF : ℕ → ℕ := schedFaultAt d C₀ σ
  rcases hfifo with hnone | ⟨j, j', hj, hj', hjlt⟩
  · -- CASE A:`q'` 永不再请求
    have hq'ne_s : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q' := by
      intro s hs hlen
      have hnone' := nextUse_eq_none_iff.mp hnone
      apply hnone' (σ.getD s 0)
      have hget : (σ.drop (t + 1)).getD (s - (t + 1)) 0 = σ.getD s 0 := by
        rw [getD_drop]
        rw [Nat.add_sub_of_le hs]
      rw [← hget]
      have hlt' : s - (t + 1) < (σ.drop (t + 1)).length := by
        rw [List.length_drop]
        omega
      rw [List.getD_eq_getElem _ 0 hlt']
      exact List.getElem_mem hlt'
    by_cases hqreq : ∃ j, nextUse σ (t + 1) q = some j
    · -- q 会被请求:好事件在 J 补偿一切
      rcases hqreq with ⟨j, hj⟩
      have hJlen : t + 1 + j < σ.length := by
        have hjlt' : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
        rw [List.length_drop] at hjlt'
        omega
      have hJle : t + 1 + j + 1 ≤ σ.length := by omega
      have hq'neA : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
        intro k hk1 hk2
        exact hq'ne_s k hk1 (by omega)
      -- 逐点:s ≤ t 时 fault 相等
      have hP0 : ∀ s, s ≤ t → eF s = dF s := by
        intro s hs
        unfold eF dF e schedFaultAt
        rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hs]
      -- 逐点:t < s < J 时 fault 相等(窗口)
      have hP1 : ∀ s, t < s → s < t + 1 + j → eF s = dF s := by
        intro s hst hsJ
        unfold eF dF e schedFaultAt
        rw [exchangeSchedule_window d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neA
          (s := s) hst (by omega)]
        have hne1 : σ.getD s 0 ≠ q := getD_ne_nextUse hj (by omega) hsJ
        have hne2 : σ.getD s 0 ≠ q' := hq'neA s (by omega) hsJ
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · rw [if_pos hr]
          have hrE' : σ.getD s 0 ∈ insert q ((schedCache d C₀ σ s).erase q') := by
            rw [Finset.mem_insert]
            right
            rw [Finset.mem_erase]
            constructor
            · exact hne2
            · exact hr
          rw [if_pos hrE']
        · rw [if_neg hr]
          have hrE' : σ.getD s 0 ∉ insert q ((schedCache d C₀ σ s).erase q') := by
            intro hm
            rcases Finset.mem_insert.mp hm with hqeq | hmem
            · exact hne1 hqeq
            · exact hr (Finset.mem_erase.mp hmem).2
          rw [if_neg hrE']
      -- 逐点:J < s 时 eF ≤ dF(无坏事件)
      have hP3A : ∀ s, t < s → s < σ.length → eF s ≤ dF s := by
        intro s hst hlen
        unfold eF dF e schedFaultAt
        by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
        · by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
          · rw [if_pos hrE, if_pos hr]
          · rw [if_neg hrE, if_pos hr]
            exfalso
            have hqqq' : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
              by_contra hnot
              have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
              exact hrE (hinv (σ.getD s 0) (by
                intro hmem2
                apply hnot
                rcases Finset.mem_insert.mp hmem2 with hqeq | hq'eq
                · exact Or.inr hqeq
                · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hr)
            rcases hqqq' with hq'eq | hqeq
            · exact hq'ne_s s (by omega) hlen hq'eq
            · have hqE : q ∈ schedCache e C₀ σ s := by
                exact exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neA
                  s hst (hqeq ▸ hr)
              exact hrE (hqeq ▸ hqE)
        · rw [if_neg hr]
          by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
          · rw [if_pos hrE]
            omega
          · rw [if_neg hrE]
      -- 好事件在 J
      have hgood := exchangeSchedule_good d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neA
      -- 拆分求和
      have hdisj : Disjoint (Finset.range (t + 1 + j + 1))
          (Finset.Ico (t + 1 + j + 1) σ.length) := by
        rw [Finset.disjoint_left]
        intro s hs1 hs2
        have h1 : s < t + 1 + j + 1 := Finset.mem_range.mp hs1
        have h2 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs2).1
        omega
      have hunion : Finset.range (t + 1 + j + 1) ∪ Finset.Ico (t + 1 + j + 1) σ.length =
          Finset.range σ.length := by
        ext s
        simp [Finset.mem_Ico]
        constructor
        · intro h
          rcases h with hs | ⟨h1, h2⟩
          · omega
          · exact h2
        · intro hs
          by_cases hs' : s < t + 1 + j + 1
          · exact Or.inl (Nat.lt_succ_iff.mp hs')
          · right
            constructor
            · omega
            · exact hs
      have hsum_e : (∑ s ∈ Finset.range σ.length, eF s) =
          (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) +
            ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s := by
        rw [← hunion, Finset.sum_union hdisj]
      have hsum_d : (∑ s ∈ Finset.range σ.length, dF s) =
          (∑ s ∈ Finset.range (t + 1 + j + 1), dF s) +
            ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
        rw [← hunion, Finset.sum_union hdisj]
      -- 第一部分:Σ_{<J+1} eF + 1 ≤ Σ_{<J+1} dF
      have hpart1 : (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) + 1 ≤
          ∑ s ∈ Finset.range (t + 1 + j + 1), dF s := by
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        have heJ : eF (t + 1 + j) = 0 := by
          unfold eF schedFaultAt
          rw [if_pos hgood.1]
        have hdJ : dF (t + 1 + j) = 1 := by
          unfold dF schedFaultAt
          rw [if_neg hgood.2]
        rw [heJ, hdJ]
        have hle : (∑ s ∈ Finset.range (t + 1 + j), eF s) ≤
            ∑ s ∈ Finset.range (t + 1 + j), dF s := by
          exact Finset.sum_le_sum (fun s hs => by
            by_cases hst' : s ≤ t
            · exact le_of_eq (hP0 s hst')
            · have hts' : t < s := by omega
              exact le_of_eq (hP1 s hts' (Finset.mem_range.mp hs)))
        have hle' : (∑ s ∈ Finset.range (t + 1 + j), eF s) + 1 ≤
            (∑ s ∈ Finset.range (t + 1 + j), dF s) + 1 := Nat.add_le_add_right hle 1
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
      -- 第二部分:Σ_{[J+1,len)} eF ≤ Σ dF
      have hpart2 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s) ≤
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
        apply Finset.sum_le_sum
        intro s hs
        have hst' : t < s := by
          have h1 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs).1
          omega
        exact hP3A s hst' (Finset.mem_Ico.mp hs).2
      -- 组装
      unfold schedMisses
      change (∑ s ∈ Finset.range σ.length, eF s) ≤ ∑ s ∈ Finset.range σ.length, dF s
      rw [hsum_e, hsum_d]
      omega
    · -- q 也不会被请求:无 q 请求、无 q' 请求,逐点比较即可
      have hqne_s : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q := by
        intro s hs hlen
        have hnoneq : nextUse σ (t + 1) q = none := by
          cases hopt : nextUse σ (t + 1) q with
          | none => rfl
          | some j => exact False.elim (hqreq ⟨j, hopt⟩)
        have hnoneq' := nextUse_eq_none_iff.mp hnoneq
        apply hnoneq' (σ.getD s 0)
        have hget : (σ.drop (t + 1)).getD (s - (t + 1)) 0 = σ.getD s 0 := by
          rw [getD_drop]
          rw [Nat.add_sub_of_le hs]
        rw [← hget]
        have hlt' : s - (t + 1) < (σ.drop (t + 1)).length := by
          rw [List.length_drop]
          omega
        rw [List.getD_eq_getElem _ 0 hlt']
        exact List.getElem_mem hlt'
      -- 逐点 eF ≤ dF
      have hP : ∀ s, s < σ.length → eF s ≤ dF s := by
        intro s hlen
        by_cases hst : s ≤ t
        · -- cache 相等
          unfold eF dF e schedFaultAt
          rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hst]
        · have hts' : t < s := by omega
          unfold eF dF e schedFaultAt
          by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
          · by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hrE, if_pos hr]
            · rw [if_neg hrE, if_pos hr]
              exfalso
              have hqqq' : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
                by_contra hnot
                have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
                exact hrE (hinv (σ.getD s 0) (by
                  intro hmem2
                  apply hnot
                  rcases Finset.mem_insert.mp hmem2 with hqeq | hq'eq
                  · exact Or.inr hqeq
                  · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hr)
              rcases hqqq' with hq'eq | hqeq
              · exact hq'ne_s s (by omega) hlen hq'eq
              · exact hqne_s s (by omega) hlen hqeq
          · rw [if_neg hr]
            by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hrE]
              omega
            · rw [if_neg hrE]
      unfold schedMisses
      change (∑ s ∈ Finset.range σ.length, eF s) ≤ ∑ s ∈ Finset.range σ.length, dF s
      exact Finset.sum_le_sum (fun s hs => hP s (Finset.mem_range.mp hs))
  · -- CASE B:`q` 的首次请求在 `q'` 的首次请求之前
    have hJlen : t + 1 + j < σ.length := by
      have hjlt' : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
      rw [List.length_drop] at hjlt'
      omega
    have hJ'len : t + 1 + j' < σ.length := by
      have hj'lt' : j' < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj').1
      rw [List.length_drop] at hj'lt'
      omega
    have hJle : t + 1 + j + 1 ≤ σ.length := by omega
    have hJ'le : t + 1 + j' + 1 ≤ σ.length := by omega
    have hJJ' : t + 1 + j + 1 ≤ t + 1 + j' := by omega
    have hq'neB : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact getD_ne_nextUse hj' hk1 (by omega)
    -- 逐点:s ≤ t 时 fault 相等
    have hP0 : ∀ s, s ≤ t → eF s = dF s := by
      intro s hs
      unfold eF dF e schedFaultAt
      rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hs]
    -- 逐点:t < s < J 时 fault 相等(窗口)
    have hP1 : ∀ s, t < s → s < t + 1 + j → eF s = dF s := by
      intro s hst hsJ
      unfold eF dF e schedFaultAt
      rw [exchangeSchedule_window d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neB
        (s := s) hst (by omega)]
      have hne1 : σ.getD s 0 ≠ q := getD_ne_nextUse hj (by omega) hsJ
      have hne2 : σ.getD s 0 ≠ q' := hq'neB s (by omega) hsJ
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · rw [if_pos hr]
        have hrE' : σ.getD s 0 ∈ insert q ((schedCache d C₀ σ s).erase q') := by
          rw [Finset.mem_insert]
          right
          rw [Finset.mem_erase]
          constructor
          · exact hne2
          · exact hr
        rw [if_pos hrE']
      · rw [if_neg hr]
        have hrE' : σ.getD s 0 ∉ insert q ((schedCache d C₀ σ s).erase q') := by
          intro hm
          rcases Finset.mem_insert.mp hm with hqeq | hmem
          · exact hne1 hqeq
          · exact hr (Finset.mem_erase.mp hmem).2
        rw [if_neg hrE']
    -- 逐点:s ≠ J' 时 eF ≤ dF(坏事件只在 J')
    have hP3 : ∀ s, t < s → s < σ.length → s ≠ t + 1 + j' → eF s ≤ dF s := by
      intro s hst hlen hsne
      unfold eF dF e schedFaultAt
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hrE, if_pos hr]
        · rw [if_neg hrE, if_pos hr]
          exfalso
          exact hsne (exchangeSchedule_bad d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neB hj'
            hst hr hrE)
      · rw [if_neg hr]
        by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hrE]
          omega
        · rw [if_neg hrE]
    -- 好事件在 J
    have hgood := exchangeSchedule_good d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neB
    -- 拆分求和
    have hdisj : Disjoint (Finset.range (t + 1 + j + 1))
        (Finset.Ico (t + 1 + j + 1) σ.length) := by
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      have h1 : s < t + 1 + j + 1 := Finset.mem_range.mp hs1
      have h2 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs2).1
      omega
    have hunion : Finset.range (t + 1 + j + 1) ∪ Finset.Ico (t + 1 + j + 1) σ.length =
        Finset.range σ.length := by
      ext s
      simp [Finset.mem_Ico]
      constructor
      · intro h
        rcases h with hs | ⟨h1, h2⟩
        · omega
        · exact h2
      · intro hs
        by_cases hs' : s < t + 1 + j + 1
        · exact Or.inl (Nat.lt_succ_iff.mp hs')
        · right
          constructor
          · omega
          · exact hs
    have hsum_e : (∑ s ∈ Finset.range σ.length, eF s) =
        (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) +
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s := by
      rw [← hunion, Finset.sum_union hdisj]
    have hsum_d : (∑ s ∈ Finset.range σ.length, dF s) =
        (∑ s ∈ Finset.range (t + 1 + j + 1), dF s) +
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
      rw [← hunion, Finset.sum_union hdisj]
    -- 第一部分:Σ_{<J+1} eF + 1 ≤ Σ_{<J+1} dF
    have hpart1 : (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) + 1 ≤
        ∑ s ∈ Finset.range (t + 1 + j + 1), dF s := by
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      have heJ : eF (t + 1 + j) = 0 := by
        unfold eF schedFaultAt
        rw [if_pos hgood.1]
      have hdJ : dF (t + 1 + j) = 1 := by
        unfold dF schedFaultAt
        rw [if_neg hgood.2]
      rw [heJ, hdJ]
      have hle : (∑ s ∈ Finset.range (t + 1 + j), eF s) ≤
          ∑ s ∈ Finset.range (t + 1 + j), dF s := by
        exact Finset.sum_le_sum (fun s hs => by
          by_cases hst' : s ≤ t
          · exact le_of_eq (hP0 s hst')
          · have hts' : t < s := by omega
            exact le_of_eq (hP1 s hts' (Finset.mem_range.mp hs)))
      have hle' : (∑ s ∈ Finset.range (t + 1 + j), eF s) + 1 ≤
          (∑ s ∈ Finset.range (t + 1 + j), dF s) + 1 := Nat.add_le_add_right hle 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
    -- 第二部分:Σ_{[J+1,len)} eF ≤ Σ dF + 1
    have hpart2 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s) ≤
        (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s) + 1 := by
      have hper : ∀ s ∈ Finset.Ico (t + 1 + j + 1) σ.length,
          eF s ≤ dF s + (if s = t + 1 + j' then 1 else 0) := by
        intro s hs
        have hst' : t < s := by
          have h1 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs).1
          exact lt_of_lt_of_le (by omega : t < t + 1 + j + 1) h1
        by_cases hsne : s = t + 1 + j'
        · subst s
          unfold eF dF schedFaultAt
          dsimp [e]
          by_cases hr : σ.getD (t + 1 + j') 0 ∈ schedCache d C₀ σ (t + 1 + j')
          · by_cases hrE : σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j')
            · rw [if_pos hrE, if_pos hr]
              norm_num
            · rw [if_neg hrE, if_pos hr]
              norm_num
          · by_cases hrE : σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j')
            · rw [if_pos hrE, if_neg hr]
              norm_num
            · rw [if_neg hrE, if_neg hr]
              norm_num
        · have hle := hP3 s hst' (Finset.mem_Ico.mp hs).2 hsne
          have hif : (if s = t + 1 + j' then 1 else 0) = 0 := if_neg hsne
          rw [hif]
          exact hle
      have hsum1 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s) ≤
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length,
            (dF s + (if s = t + 1 + j' then 1 else 0)) := by
        exact Finset.sum_le_sum hper
      have hsum2 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length,
            (dF s + (if s = t + 1 + j' then 1 else 0))) =
          (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s) +
            ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, (if s = t + 1 + j' then 1 else 0) := by
        rw [Finset.sum_add_distrib]
      have hsum3 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, (if s = t + 1 + j' then 1 else 0)) ≤ 1 := by
        rw [Finset.sum_ite_eq']
        by_cases hJ'in : t + 1 + j' ∈ Finset.Ico (t + 1 + j + 1) σ.length
        · simp [hJ'in]
        · simp [hJ'in]
      rw [hsum2] at hsum1
      exact le_trans hsum1 (Nat.add_le_add_left hsum3 _)
    -- 组装
    unfold schedMisses
    change (∑ s ∈ Finset.range σ.length, eF s) ≤ ∑ s ∈ Finset.range σ.length, dF s
    rw [hsum_e, hsum_d]
    have hboth : (∑ s ∈ Finset.range σ.length, eF s) + 1 ≤
        (∑ s ∈ Finset.range σ.length, dF s) + 1 := by
      rw [hsum_e, hsum_d]
      have h := add_le_add hpart1 hpart2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    omega

/-- The farthest-in-future (Belady) eviction schedule for `σ` from `C₀`. -/
noncomputable def fifoSchedule (σ : List Page) (C₀ : Finset Page) : ℕ → Page :=
  policySchedule (fifoPolicy σ) C₀ σ

/-- `d` agrees with the farthest-in-future schedule on caches through `n`. -/
def agreeWithFIF (d : ℕ → Page) (C₀ : Finset Page) (σ : List Page) (n : ℕ) : Prop :=
  ∀ s ≤ n, schedCache d C₀ σ s = schedCache (fifoSchedule σ C₀) C₀ σ s

/-- The run of the FIF schedule is the run of the FIF policy. -/
lemma schedCache_fifoSchedule (σ : List Page) (C₀ : Finset Page) (s : ℕ) :
    schedCache (fifoSchedule σ C₀) C₀ σ s = cacheSeq (fifoPolicy σ) C₀ σ s := by
  unfold fifoSchedule
  exact schedCache_policySchedule (fifoPolicy σ) C₀ σ s

/-- When `d` agrees with the FIF schedule through `t`, the FIF eviction at `t`
is the farthest-in-future page of `d`'s cache. -/
lemma fifo_evict_eq_farthest (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    {t : ℕ} (hagree : agreeWithFIF d C₀ σ t) :
    (fifoSchedule σ C₀) t = farthestInFuture (schedCache d C₀ σ t) σ t := by
  change farthestInFuture (cacheSeq (fifoPolicy σ) C₀ σ t) σ t =
    farthestInFuture (schedCache d C₀ σ t) σ t
  rw [← schedCache_fifoSchedule σ C₀ t]
  rw [← hagree t le_rfl]

/-- The caches in a run of a reduced schedule from a nonempty cache are
nonempty. -/
lemma schedCache_nonempty_of_reduced (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty) (s : ℕ) : (schedCache d C₀ σ s).Nonempty := by
  cases s with
  | zero => exact hC₀
  | succ s =>
      rw [schedCache]
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · rw [if_pos hr]
        exact ⟨σ.getD s 0, hr⟩
      · rw [if_neg hr]
        exact ⟨σ.getD s 0, Finset.mem_insert_self _ _⟩

/-- At a first disagreement `t` of a reduced schedule `d` with the FIF
schedule, both fault at `t`, the evictions differ, and the FIF eviction is
resident in `d`'s cache. -/
lemma first_disagree (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1)) :
    σ.getD t 0 ∉ schedCache d C₀ σ t ∧
    d t ≠ (fifoSchedule σ C₀) t ∧
    (fifoSchedule σ C₀) t ∈ schedCache d C₀ σ t := by
  have hft : σ.getD t 0 ∉ schedCache d C₀ σ t := by
    intro hft
    have hFt : σ.getD t 0 ∈ schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [← hagree t le_rfl]
      exact hft
    have hD : schedCache d C₀ σ (t + 1) = schedCache d C₀ σ t := by
      rw [schedCache]
      rw [if_pos hft]
    have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
        schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [schedCache]
      rw [if_pos hFt]
    exact hdis ((hD.trans (hagree t le_rfl)).trans hF.symm)
  constructor
  · exact hft
  · constructor
    · intro hq
      have hFt : σ.getD t 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ t := by
        rw [← hagree t le_rfl]
        exact hft
      have hD : schedCache d C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache d C₀ σ t).erase (d t)) := by
        rw [schedCache]
        rw [if_neg hft]
      have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache (fifoSchedule σ C₀) C₀ σ t).erase
            ((fifoSchedule σ C₀) t)) := by
        rw [schedCache]
        rw [if_neg hFt]
      have hEq : schedCache d C₀ σ t = schedCache (fifoSchedule σ C₀) C₀ σ t :=
        hagree t le_rfl
      rw [hD, hF] at hdis
      rw [hEq] at hdis
      rw [hq] at hdis
      exact hdis rfl
    · rw [fifo_evict_eq_farthest d σ C₀ hagree]
      apply mem_farthestInFuture
      exact schedCache_nonempty_of_reduced d σ C₀ hC₀ t

/-- Exchanging the first disagreement of a reduced schedule never increases
misses and extends agreement with the FIF schedule by one position. -/
lemma exchange_step (d : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hdreduced : ∀ s, σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF d C₀ σ t)
    (hdis : schedCache d C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1)) :
    schedMisses (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ ≤
      schedMisses d C₀ σ ∧
    agreeWithFIF (exchangeSchedule d t (d t) (fifoSchedule σ C₀ t) σ C₀) C₀ σ (t + 1) := by
  let q : Page := d t
  let q' : Page := fifoSchedule σ C₀ t
  have hfd := first_disagree d σ C₀ hC₀ ht hagree hdis
  have hqq' : q ≠ q' := hfd.2.1
  have hft : σ.getD t 0 ∉ schedCache d C₀ σ t := hfd.1
  have hq'res : q' ∈ schedCache d C₀ σ t := hfd.2.2
  have hfifo : nextUse σ (t + 1) q' = none ∨
      ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' := by
    apply fifo_nextUse_order σ (schedCache d C₀ σ t) t q' q
    · exact fifo_evict_eq_farthest d σ C₀ hagree
    · exact hdreduced t hft
    · exact hqq'
  constructor
  · exact exchangeSchedule_misses_le d t q q' σ C₀ rfl hqq'
      (fun s hs hr => hdreduced s hr) hft hq'res hfifo
  · intro s hs
    by_cases hs' : s ≤ t
    · rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hs']
      exact hagree s hs'
    · have hst : s = t + 1 := by omega
      subst s
      have hFt : σ.getD t 0 ∉ schedCache (fifoSchedule σ C₀) C₀ σ t := by
        rw [← hagree t le_rfl]
        exact hft
      have hE : schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q') := by
        rw [schedCache_exchangeScheduleCore, exchangeScheduleCore]
        dsimp
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).1 = schedCache d C₀ σ t by
          rw [← schedCache_exchangeScheduleCore]
          exact schedCache_exchangeSchedule_eq_d d t q q' σ C₀ le_rfl]
        rw [show (exchangeScheduleCore d t q q' σ C₀ t).2 = q' by
          exact exchangeSchedule_at_t d t q q' σ C₀]
        rw [if_neg hft]
      have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache d C₀ σ t).erase q') := by
        rw [schedCache_fifoSchedule σ C₀ (t + 1)]
        unfold cacheSeq Policy.step
        rw [← schedCache_fifoSchedule σ C₀ t]
        rw [if_neg hFt]
        congr 2
        · rw [← hagree t le_rfl]
        · change farthestInFuture (schedCache (fifoSchedule σ C₀) C₀ σ t) σ t = q'
          rw [← hagree t le_rfl]
          rw [← fifo_evict_eq_farthest d σ C₀ hagree]
      rw [hE, hF]

/-- The exchange schedule is reduced at every fault after the first `q'`
request: from `J'` on, `q'` is resident whenever `d` evicts it, and the
multi-set branches always evict resident pages. -/
lemma exchangeSchedule_reduced_after (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    {j : ℕ} (hj : nextUse σ (t + 1) q = some j)
    (hq'ne : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q')
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    {s : ℕ} (hsJ' : t + 1 + j' < s)
    (hFault : σ.getD s 0 ∉ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) :
    exchangeSchedule d t q q' σ C₀ s ∈ schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  let C' : Finset Page := schedCache e C₀ σ s
  have hC' : C' = (exchangeScheduleCore d t q q' σ C₀ s).1 := by
    unfold C'
    rw [schedCache_exchangeScheduleCore]
  have hFault' : σ.getD s 0 ∉ C' := by
    simpa [C'] using hFault
  have hcard : (schedCache d C₀ σ s).card ≤ C'.card := by
    rw [hC']
    exact exchangeScheduleCore_card d t q q' σ C₀ hweak (by omega)
  -- a request that `d` serves from the cache is `q` or `q'`
  have hsig_in : σ.getD s 0 ∈ schedCache d C₀ σ s → σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
    intro hsigD
    by_contra hnot
    have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
    have hmem : σ.getD s 0 ∈ C' := by
      simpa [e, C'] using hinv (σ.getD s 0) (by
        intro hmem
        apply hnot
        rcases Finset.mem_insert.mp hmem with hqeq | hq'eq
        · exact Or.inr hqeq
        · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hsigD
    exact hFault' hmem
  -- resident pages of `d` are resident in the exchange cache
  have hq_memD : q ∈ schedCache d C₀ σ s → q ∈ C' := by
    intro hqD
    have hmem := exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'ne
      s (by omega) hqD
    simpa [e, C'] using hmem
  have hq'_memD : q' ∈ schedCache d C₀ σ s → q' ∈ C' := by
    intro hq'D
    have hmem := exchangeSchedule_q'_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'ne hj'
      s hsJ' hq'D
    simpa [e, C'] using hmem
  -- `d` cannot hit at `s` (the exchange schedule faults there)
  have hdFault : σ.getD s 0 ∉ schedCache d C₀ σ s := by
    intro hdHit
    rcases hsig_in hdHit with hq'eq | hqeq
    · exact hFault' (hq'eq ▸ hq'_memD (hq'eq ▸ hdHit))
    · exact hFault' (hqeq ▸ hq_memD (hqeq ▸ hdHit))
  -- branch analysis of the exchange decision
  change (exchangeScheduleCore d t q q' σ C₀ s).2 ∈
    schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s
  rw [exchangeScheduleCore_second]
  rw [← hC']
  change exchangeDecision d t q q' σ C₀ C' s ∈ C'
  unfold exchangeDecision
  have hlt : ¬ s < t := by omega
  have hne : ¬ s = t := by omega
  rw [if_neg hlt, if_neg hne]
  by_cases h1 : d s = q'
  · rw [if_pos h1]
    -- d faults at s, so q' ∈ D(s), hence q' ∈ E(s)
    have hq'inD : q' ∈ schedCache d C₀ σ s := by
      have hd : d s ∈ schedCache d C₀ σ s := hweak s (by omega) hdFault
      rwa [h1] at hd
    exact hq'_memD hq'inD
  · rw [if_neg h1]
    by_cases hb4 : (σ.getD s 0 = q' ∨ σ.getD s 0 = q) ∧
        σ.getD s 0 ∈ schedCache d C₀ σ s
    · rw [if_pos hb4]
      by_cases hf : ((C' \ schedCache d C₀ σ s).filter (fun x => x ≠ q')).Nonempty
      · rw [dif_pos hf]
        have hspec := Classical.choose_spec hf
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hspec).1).1
      · rw [dif_neg hf]
        by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
        · rw [dif_pos hm]
          exact (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
        · rw [dif_neg hm]
          exfalso
          have hsub : C' ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hEq : C' = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          exact hFault' (hEq ▸ hb4.2)
    · rw [if_neg hb4]
      by_cases h5 : d s ∈ C'
      · rw [if_pos h5]
        exact h5
      · rw [if_neg h5]
        by_cases hm : (C' \ schedCache d C₀ σ s).Nonempty
        · rw [dif_pos hm]
          exact (Finset.mem_sdiff.mp (Classical.choose_spec hm)).1
        · rw [dif_neg hm]
          exfalso
          have hsub : C' ⊆ schedCache d C₀ σ s := by
            intro y hy
            by_contra hyn
            exact hm ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyn⟩⟩
          have hEq : C' = schedCache d C₀ σ s :=
            Finset.eq_of_subset_of_card_le hsub hcard
          exact h5 (hEq ▸ hweak s (by omega) hdFault)

/-- The exchange has a spare miss when the bad event did not occur: either
`q'` is never requested again and `q` is, or `d` evicts `q'` before its first
request (so `d` misses there too). -/
lemma exchangeSchedule_misses_le_plus_one (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ : Finset Page)
    (hq : d t = q) (hqq' : q ≠ q')
    (hweak : ∀ s, t ≤ s → σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (hft : σ.getD t 0 ∉ schedCache d C₀ σ t)
    (hq'res : q' ∈ schedCache d C₀ σ t)
    (hslack : (nextUse σ (t + 1) q' = none ∧ ∃ j, nextUse σ (t + 1) q = some j) ∨
      ∃ j j', nextUse σ (t + 1) q = some j ∧ nextUse σ (t + 1) q' = some j' ∧ j < j' ∧
        σ.getD (t + 1 + j') 0 ∉ schedCache d C₀ σ (t + 1 + j')) :
    schedMisses (exchangeSchedule d t q q' σ C₀) C₀ σ + 1 ≤ schedMisses d C₀ σ := by
  let e : ℕ → Page := exchangeSchedule d t q q' σ C₀
  let eF : ℕ → ℕ := schedFaultAt e C₀ σ
  let dF : ℕ → ℕ := schedFaultAt d C₀ σ
  rcases hslack with ⟨hnone, hqreq⟩ | ⟨j, j', hj, hj', hjlt, hnoBad⟩
  · -- CASE A:`q'` 永不再请求
    have hq'ne_s : ∀ s, t + 1 ≤ s → s < σ.length → σ.getD s 0 ≠ q' := by
      intro s hs hlen
      have hnone' := nextUse_eq_none_iff.mp hnone
      apply hnone' (σ.getD s 0)
      have hget : (σ.drop (t + 1)).getD (s - (t + 1)) 0 = σ.getD s 0 := by
        rw [getD_drop]
        rw [Nat.add_sub_of_le hs]
      rw [← hget]
      have hlt' : s - (t + 1) < (σ.drop (t + 1)).length := by
        rw [List.length_drop]
        omega
      rw [List.getD_eq_getElem _ 0 hlt']
      exact List.getElem_mem hlt'
    rcases hqreq with ⟨j, hj⟩
    have hJlen : t + 1 + j < σ.length := by
      have hjlt' : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
      rw [List.length_drop] at hjlt'
      omega
    have hJle : t + 1 + j + 1 ≤ σ.length := by omega
    have hq'neA : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact hq'ne_s k hk1 (by omega)
    -- 逐点:s ≤ t 时 fault 相等
    have hP0 : ∀ s, s ≤ t → eF s = dF s := by
      intro s hs
      unfold eF dF e schedFaultAt
      rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hs]
    -- 逐点:t < s < J 时 fault 相等(窗口)
    have hP1 : ∀ s, t < s → s < t + 1 + j → eF s = dF s := by
      intro s hst hsJ
      unfold eF dF e schedFaultAt
      rw [exchangeSchedule_window d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neA
        (s := s) hst (by omega)]
      have hne1 : σ.getD s 0 ≠ q := getD_ne_nextUse hj (by omega) hsJ
      have hne2 : σ.getD s 0 ≠ q' := hq'neA s (by omega) hsJ
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · rw [if_pos hr]
        have hrE' : σ.getD s 0 ∈ insert q ((schedCache d C₀ σ s).erase q') := by
          rw [Finset.mem_insert]
          right
          rw [Finset.mem_erase]
          constructor
          · exact hne2
          · exact hr
        rw [if_pos hrE']
      · rw [if_neg hr]
        have hrE' : σ.getD s 0 ∉ insert q ((schedCache d C₀ σ s).erase q') := by
          intro hm
          rcases Finset.mem_insert.mp hm with hqeq | hmem
          · exact hne1 hqeq
          · exact hr (Finset.mem_erase.mp hmem).2
        rw [if_neg hrE']
    -- 逐点:J < s 时 eF ≤ dF(无坏事件)
    have hP3A : ∀ s, t < s → s < σ.length → eF s ≤ dF s := by
      intro s hst hlen
      unfold eF dF e schedFaultAt
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hrE, if_pos hr]
        · rw [if_neg hrE, if_pos hr]
          exfalso
          have hqqq' : σ.getD s 0 = q' ∨ σ.getD s 0 = q := by
            by_contra hnot
            have hinv := exchangeSchedule_invariant d t q q' σ C₀ hq hweak s (by omega)
            exact hrE (hinv (σ.getD s 0) (by
              intro hmem2
              apply hnot
              rcases Finset.mem_insert.mp hmem2 with hqeq | hq'eq
              · exact Or.inr hqeq
              · exact Or.inl (Finset.mem_singleton.mp hq'eq)) hr)
          rcases hqqq' with hq'eq | hqeq
          · exact hq'ne_s s (by omega) hlen hq'eq
          · have hqE : q ∈ schedCache e C₀ σ s := by
              exact exchangeSchedule_q_mem d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neA
                s hst (hqeq ▸ hr)
            exact hrE (hqeq ▸ hqE)
      · rw [if_neg hr]
        by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hrE]
          omega
        · rw [if_neg hrE]
    -- 好事件在 J
    have hgood := exchangeSchedule_good d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neA
    -- 拆分求和
    have hdisj : Disjoint (Finset.range (t + 1 + j + 1))
        (Finset.Ico (t + 1 + j + 1) σ.length) := by
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      have h1 : s < t + 1 + j + 1 := Finset.mem_range.mp hs1
      have h2 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs2).1
      omega
    have hunion : Finset.range (t + 1 + j + 1) ∪ Finset.Ico (t + 1 + j + 1) σ.length =
        Finset.range σ.length := by
      ext s
      simp [Finset.mem_Ico]
      constructor
      · intro h
        rcases h with hs | ⟨h1, h2⟩
        · omega
        · exact h2
      · intro hs
        by_cases hs' : s < t + 1 + j + 1
        · exact Or.inl (Nat.lt_succ_iff.mp hs')
        · right
          constructor
          · omega
          · exact hs
    have hsum_e : (∑ s ∈ Finset.range σ.length, eF s) =
        (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) +
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s := by
      rw [← hunion, Finset.sum_union hdisj]
    have hsum_d : (∑ s ∈ Finset.range σ.length, dF s) =
        (∑ s ∈ Finset.range (t + 1 + j + 1), dF s) +
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
      rw [← hunion, Finset.sum_union hdisj]
    -- 第一部分:Σ_{<J+1} eF + 1 ≤ Σ_{<J+1} dF
    have hpart1 : (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) + 1 ≤
        ∑ s ∈ Finset.range (t + 1 + j + 1), dF s := by
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      have heJ : eF (t + 1 + j) = 0 := by
        unfold eF schedFaultAt
        rw [if_pos hgood.1]
      have hdJ : dF (t + 1 + j) = 1 := by
        unfold dF schedFaultAt
        rw [if_neg hgood.2]
      rw [heJ, hdJ]
      have hle : (∑ s ∈ Finset.range (t + 1 + j), eF s) ≤
          ∑ s ∈ Finset.range (t + 1 + j), dF s := by
        exact Finset.sum_le_sum (fun s hs => by
          by_cases hst' : s ≤ t
          · exact le_of_eq (hP0 s hst')
          · have hts' : t < s := by omega
            exact le_of_eq (hP1 s hts' (Finset.mem_range.mp hs)))
      have hle' : (∑ s ∈ Finset.range (t + 1 + j), eF s) + 1 ≤
          (∑ s ∈ Finset.range (t + 1 + j), dF s) + 1 := Nat.add_le_add_right hle 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
    -- 第二部分:Σ_{[J+1,len)} eF ≤ Σ dF
    have hpart2 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s) ≤
        ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
      apply Finset.sum_le_sum
      intro s hs
      have hst' : t < s := by
        have h1 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs).1
        omega
      exact hP3A s hst' (Finset.mem_Ico.mp hs).2
    -- 组装
    unfold schedMisses
    change (∑ s ∈ Finset.range σ.length, eF s) + 1 ≤ ∑ s ∈ Finset.range σ.length, dF s
    rw [hsum_e, hsum_d]
    have h := add_le_add hpart1 hpart2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

  · -- CASE B:`q` 的首次请求在 `q'` 的首次请求之前
    have hJlen : t + 1 + j < σ.length := by
      have hjlt' : j < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj).1
      rw [List.length_drop] at hjlt'
      omega
    have hJ'len : t + 1 + j' < σ.length := by
      have hj'lt' : j' < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj').1
      rw [List.length_drop] at hj'lt'
      omega
    have hJle : t + 1 + j + 1 ≤ σ.length := by omega
    have hJ'le : t + 1 + j' + 1 ≤ σ.length := by omega
    have hJJ' : t + 1 + j + 1 ≤ t + 1 + j' := by omega
    have hq'neB : ∀ k, t + 1 ≤ k → k < t + 1 + j → σ.getD k 0 ≠ q' := by
      intro k hk1 hk2
      exact getD_ne_nextUse hj' hk1 (by omega)
    -- 逐点:s ≤ t 时 fault 相等
    have hP0 : ∀ s, s ≤ t → eF s = dF s := by
      intro s hs
      unfold eF dF e schedFaultAt
      rw [schedCache_exchangeSchedule_eq_d d t q q' σ C₀ hs]
    -- 逐点:t < s < J 时 fault 相等(窗口)
    have hP1 : ∀ s, t < s → s < t + 1 + j → eF s = dF s := by
      intro s hst hsJ
      unfold eF dF e schedFaultAt
      rw [exchangeSchedule_window d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neB
        (s := s) hst (by omega)]
      have hne1 : σ.getD s 0 ≠ q := getD_ne_nextUse hj (by omega) hsJ
      have hne2 : σ.getD s 0 ≠ q' := hq'neB s (by omega) hsJ
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · rw [if_pos hr]
        have hrE' : σ.getD s 0 ∈ insert q ((schedCache d C₀ σ s).erase q') := by
          rw [Finset.mem_insert]
          right
          rw [Finset.mem_erase]
          constructor
          · exact hne2
          · exact hr
        rw [if_pos hrE']
      · rw [if_neg hr]
        have hrE' : σ.getD s 0 ∉ insert q ((schedCache d C₀ σ s).erase q') := by
          intro hm
          rcases Finset.mem_insert.mp hm with hqeq | hmem
          · exact hne1 hqeq
          · exact hr (Finset.mem_erase.mp hmem).2
        rw [if_neg hrE']
    -- 逐点:s ≠ J' 时 eF ≤ dF(坏事件只在 J')
    have hP3 : ∀ s, t < s → s < σ.length → s ≠ t + 1 + j' → eF s ≤ dF s := by
      intro s hst hlen hsne
      unfold eF dF e schedFaultAt
      by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
      · by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hrE, if_pos hr]
        · rw [if_neg hrE, if_pos hr]
          exfalso
          exact hsne (exchangeSchedule_bad d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neB hj'
            hst hr hrE)
      · rw [if_neg hr]
        by_cases hrE : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hrE]
          omega
        · rw [if_neg hrE]
    -- 好事件在 J
    have hgood := exchangeSchedule_good d t q q' σ C₀ hq hqq' hweak hft hq'res hj hq'neB
    -- 拆分求和
    have hdisj : Disjoint (Finset.range (t + 1 + j + 1))
        (Finset.Ico (t + 1 + j + 1) σ.length) := by
      rw [Finset.disjoint_left]
      intro s hs1 hs2
      have h1 : s < t + 1 + j + 1 := Finset.mem_range.mp hs1
      have h2 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs2).1
      omega
    have hunion : Finset.range (t + 1 + j + 1) ∪ Finset.Ico (t + 1 + j + 1) σ.length =
        Finset.range σ.length := by
      ext s
      simp [Finset.mem_Ico]
      constructor
      · intro h
        rcases h with hs | ⟨h1, h2⟩
        · omega
        · exact h2
      · intro hs
        by_cases hs' : s < t + 1 + j + 1
        · exact Or.inl (Nat.lt_succ_iff.mp hs')
        · right
          constructor
          · omega
          · exact hs
    have hsum_e : (∑ s ∈ Finset.range σ.length, eF s) =
        (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) +
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s := by
      rw [← hunion, Finset.sum_union hdisj]
    have hsum_d : (∑ s ∈ Finset.range σ.length, dF s) =
        (∑ s ∈ Finset.range (t + 1 + j + 1), dF s) +
          ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
      rw [← hunion, Finset.sum_union hdisj]
    -- 第一部分:Σ_{<J+1} eF + 1 ≤ Σ_{<J+1} dF
    have hpart1 : (∑ s ∈ Finset.range (t + 1 + j + 1), eF s) + 1 ≤
        ∑ s ∈ Finset.range (t + 1 + j + 1), dF s := by
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      have heJ : eF (t + 1 + j) = 0 := by
        unfold eF schedFaultAt
        rw [if_pos hgood.1]
      have hdJ : dF (t + 1 + j) = 1 := by
        unfold dF schedFaultAt
        rw [if_neg hgood.2]
      rw [heJ, hdJ]
      have hle : (∑ s ∈ Finset.range (t + 1 + j), eF s) ≤
          ∑ s ∈ Finset.range (t + 1 + j), dF s := by
        exact Finset.sum_le_sum (fun s hs => by
          by_cases hst' : s ≤ t
          · exact le_of_eq (hP0 s hst')
          · have hts' : t < s := by omega
            exact le_of_eq (hP1 s hts' (Finset.mem_range.mp hs)))
      have hle' : (∑ s ∈ Finset.range (t + 1 + j), eF s) + 1 ≤
          (∑ s ∈ Finset.range (t + 1 + j), dF s) + 1 := Nat.add_le_add_right hle 1
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle'
    -- 第二部分:Σ_{[J+1,len)} eF ≤ Σ dF + 1
    have hpart2 : (∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s) ≤
        ∑ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, dF s := by
      have hper : ∀ s ∈ Finset.Ico (t + 1 + j + 1) σ.length, eF s ≤ dF s := by
        intro s hs
        have hst' : t < s := by
          have h1 : t + 1 + j + 1 ≤ s := (Finset.mem_Ico.mp hs).1
          exact lt_of_lt_of_le (by omega : t < t + 1 + j + 1) h1
        by_cases hsne : s = t + 1 + j'
        · subst s
          unfold eF dF schedFaultAt
          dsimp [e]
          have hsig : σ.getD (t + 1 + j') 0 = q' := getD_eq_nextUse hj'
          have hnotE : σ.getD (t + 1 + j') 0 ∉ schedCache e C₀ σ (t + 1 + j') := by
            rw [hsig]
            apply exchangeSchedule_q'_absent d t q q' σ C₀ hweak hft hq'res hj'
            · omega
            · rfl
          rw [if_neg hnotE]
          rw [if_neg hnoBad]
        · exact hP3 s hst' (Finset.mem_Ico.mp hs).2 hsne
      exact Finset.sum_le_sum hper
    -- 组装
    unfold schedMisses
    change (∑ s ∈ Finset.range σ.length, eF s) + 1 ≤ ∑ s ∈ Finset.range σ.length, dF s
    rw [hsum_e, hsum_d]
    have h := add_le_add hpart1 hpart2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h


/-- The **repair schedule**: agrees with `e` everywhere except it evicts
`q'` at `t` and at `nop` (the first `q'` request; the second eviction is a
no-op that makes the cache coincide with `e`'s afterwards). -/
noncomputable def repairSchedule (e : ℕ → Page) (t : ℕ) (q' : Page) (nop : ℕ) : ℕ → Page :=
  fun s => if s = t ∨ s = nop then q' else e s

/-- The repair schedule evicts `q'` at `t`. -/
lemma repairSchedule_at_t (e : ℕ → Page) (t : ℕ) (q' : Page) (nop : ℕ) :
    repairSchedule e t q' nop t = q' := by
  unfold repairSchedule
  simp

/-- The repair schedule's cache agrees with `e`'s up to `t`. -/
lemma schedCache_repairSchedule_eq_e (e : ℕ → Page) (t : ℕ) (q' : Page) (nop : ℕ)
    (htn : t < nop) (σ : List Page) (C₀ : Finset Page) {s : ℕ} (hs : s ≤ t) :
    schedCache (repairSchedule e t q' nop) C₀ σ s = schedCache e C₀ σ s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      rw [schedCache, schedCache]
      rw [ih (by omega)]
      unfold repairSchedule
      simp [show s ≠ t by omega, show s ≠ nop by omega]

/-- The repair's cache just after `t` is `e`'s cache with `q'` removed. -/
lemma repairSchedule_base (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j') :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1) =
      (schedCache e C₀ σ (t + 1)).erase q' := by
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t := by
    intro hft
    have hFt : σ.getD t 0 ∈ schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [← hagree t le_rfl]
      exact hft
    have hD : schedCache e C₀ σ (t + 1) = schedCache e C₀ σ t := by
      rw [schedCache]
      rw [if_pos hft]
    have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
        schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [schedCache]
      rw [if_pos hFt]
    exact hdis ((hD.trans (hagree t le_rfl)).trans hF.symm)
  have hq'res : q' ∈ schedCache e C₀ σ t := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    rw [hq']
    exact hfd.2.2
  have hsig_ne : σ.getD t 0 ≠ q' := by
    intro hsig
    exact hft (hsig ▸ hq'res)
  rw [schedCache]
  rw [schedCache_repairSchedule_eq_e e t q' (t + 1 + j') (by omega) σ C₀ le_rfl]
  rw [repairSchedule_at_t]
  rw [if_neg hft]
  rw [schedCache]
  rw [if_neg hft]
  rw [Finset.erase_eq_of_notMem hnoop]
  rw [Finset.erase_insert_of_ne hsig_ne]

/-- The repair's cache step inside the window. -/
lemma repairSchedule_step (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    (s : ℕ) (ih : t < s → s ≤ t + 1 + j' →
      schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
        (schedCache e C₀ σ s).erase q')
    (hts : t < s) (hsJ' : s < t + 1 + j') :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (s + 1) =
      (schedCache e C₀ σ (s + 1)).erase q' := by
  have hsig_ne_q' : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) hsJ'
  have hds : repairSchedule e t q' (t + 1 + j') s = e s := by
    unfold repairSchedule
    simp [show s ≠ t by omega, show s ≠ t + 1 + j' by omega]
  change (if σ.getD s 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s then
      schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
    else insert (σ.getD s 0) ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s).erase
      (repairSchedule e t q' (t + 1 + j') s))) =
    (if σ.getD s 0 ∈ schedCache e C₀ σ s then schedCache e C₀ σ s
      else insert (σ.getD s 0) ((schedCache e C₀ σ s).erase (e s))).erase q'
  rw [hds]
  rw [ih hts (by omega)]
  by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
  · have hr' : σ.getD s 0 ∈ (schedCache e C₀ σ s).erase q' := by
      rw [Finset.mem_erase]
      constructor
      · exact hsig_ne_q'
      · exact hr
    rw [if_pos hr, if_pos hr']
  · rw [if_neg hr]
    have hr' : σ.getD s 0 ∉ (schedCache e C₀ σ s).erase q' := by
      intro hm
      exact hr (Finset.mem_erase.mp hm).2
    rw [if_neg hr']
    rw [Finset.erase_insert_of_ne hsig_ne_q']
    have herase_comm : ((schedCache e C₀ σ s).erase q').erase (e s) =
        ((schedCache e C₀ σ s).erase (e s)).erase q' := by
      ext x
      simp [Finset.mem_erase, and_left_comm, and_assoc]
    rw [herase_comm]

/-- In the window `(t, J']`, the repair schedule's cache is `e`'s cache with
`q'` removed. -/
lemma repairSchedule_window (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    {s : ℕ} (hs1 : t < s) (hs2 : s ≤ t + 1 + j') :
    schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s =
      (schedCache e C₀ σ s).erase q' := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t
      · subst s
        exact repairSchedule_base e σ C₀ hC₀ ht hagree hdis hnoop hq' hj'
      · exact repairSchedule_step e σ C₀ hC₀ ht hagree hdis hnoop hq' hj' s ih
          (by omega) (by omega)

/-- After the first `q'` request, the repair's cache contains `e`'s. -/
lemma repairSchedule_superset (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    (hq' : q' = fifoSchedule σ C₀ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) q' = some j')
    {s : ℕ} (hs : t + 1 + j' < s) :
    schedCache e C₀ σ s ⊆ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases hs_eq : s = t + 1 + j'
      · subst s
        -- base: the repair evicts q' at J' (a no-op) and reloads it
        have hwin : schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j') =
            (schedCache e C₀ σ (t + 1 + j')).erase q' := by
          exact repairSchedule_window e σ C₀ hC₀ ht hagree hdis hnoop hq' hj'
            (by omega) (by rfl)
        have hsig : (σ[t + 1 + j']?).getD 0 = q' := by
          simpa using getD_eq_nextUse hj'
        have hq'notE : q' ∉ (schedCache e C₀ σ (t + 1 + j')).erase q' := by
          intro hm
          exact (Finset.mem_erase.mp hm).1 rfl
        change (if σ.getD (t + 1 + j') 0 ∈ schedCache e C₀ σ (t + 1 + j') then
            schedCache e C₀ σ (t + 1 + j')
          else insert (σ.getD (t + 1 + j') 0)
            ((schedCache e C₀ σ (t + 1 + j')).erase (e (t + 1 + j')))) ⊆
          (if σ.getD (t + 1 + j') 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j')
            then schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j')
          else insert (σ.getD (t + 1 + j') 0)
            ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ (t + 1 + j')).erase
              (repairSchedule e t q' (t + 1 + j') (t + 1 + j'))))
        rw [hwin]
        unfold repairSchedule
        simp [show t + 1 + j' ≠ t by omega]
        simp [hsig]
        intro x hx
        by_cases hr : q' ∈ schedCache e C₀ σ (t + 1 + j')
        · rw [if_pos hr] at hx
          rw [Finset.mem_insert]
          by_cases hxq' : x = q'
          · left
            exact hxq'
          · right
            rw [Finset.mem_erase]
            constructor
            · exact hxq'
            · exact hx
        · rw [if_neg hr] at hx
          rcases Finset.mem_insert.mp hx with hxq' | hxin
          · rw [hxq']
            rw [Finset.mem_insert]
            left
            rfl
          · have hxin' : x ∈ (schedCache e C₀ σ (t + 1 + j')).erase (e (t + 1 + j')) :=
              hxin
            have hxE : x ∈ schedCache e C₀ σ (t + 1 + j') := (Finset.mem_erase.mp hxin').2
            have hxne_q' : x ≠ q' := by
              intro hxq'
              exact hr (hxq' ▸ hxE)
            rw [Finset.mem_insert]
            right
            rw [Finset.mem_erase]
            constructor
            · exact hxne_q'
            · exact hxE
      · -- step: s > J'
        have hsJ' : t + 1 + j' < s := by omega
        have ih' := ih hsJ'
        have hds : repairSchedule e t q' (t + 1 + j') s = e s := by
          unfold repairSchedule
          simp [show s ≠ t by omega, show s ≠ t + 1 + j' by omega]
        change (if σ.getD s 0 ∈ schedCache e C₀ σ s then schedCache e C₀ σ s
            else insert (σ.getD s 0) ((schedCache e C₀ σ s).erase (e s))) ⊆
          (if σ.getD s 0 ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s then
              schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
            else insert (σ.getD s 0) ((schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s).erase
              (repairSchedule e t q' (t + 1 + j') s)))
        rw [hds]
        intro x hx
        by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
        · rw [if_pos hr] at hx
          rw [if_pos (ih' hr)]
          exact ih' hx
        · rw [if_neg hr] at hx
          rcases Finset.mem_insert.mp hx with hxr | hxin
          · subst x
            by_cases hrE : σ.getD s 0 ∈
                schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
            · rw [if_pos hrE]
              exact hrE
            · rw [if_neg hrE]
              rw [Finset.mem_insert]
              left
              rfl
          · have hxE : x ∈ schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s :=
              ih' (Finset.mem_erase.mp hxin).2
            have hxne : x ≠ e s := (Finset.mem_erase.mp hxin).1
            by_cases hrE : σ.getD s 0 ∈
                schedCache (repairSchedule e t q' (t + 1 + j')) C₀ σ s
            · rw [if_pos hrE]
              exact hxE
            · rw [if_neg hrE]
              rw [Finset.mem_insert]
              right
              rw [Finset.mem_erase]
              constructor
              · exact hxne
              · exact hxE


lemma repair_step (e : ℕ → Page) (σ : List Page) (C₀ : Finset Page)
    (hC₀ : C₀.Nonempty)
    {t : ℕ} (ht : t < σ.length)
    (hagree : agreeWithFIF e C₀ σ t)
    (hdis : schedCache e C₀ σ (t + 1) ≠ schedCache (fifoSchedule σ C₀) C₀ σ (t + 1))
    (hnoop : e t ∉ schedCache e C₀ σ t)
    {j' : ℕ} (hj' : nextUse σ (t + 1) (fifoSchedule σ C₀ t) = some j') :
    schedMisses (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ ≤
      schedMisses e C₀ σ + 1 ∧
    agreeWithFIF (repairSchedule e t (fifoSchedule σ C₀ t) (t + 1 + j')) C₀ σ (t + 1) := by
  let q' : Page := fifoSchedule σ C₀ t
  let r : ℕ → Page := repairSchedule e t q' (t + 1 + j')
  let eF : ℕ → ℕ := schedFaultAt e C₀ σ
  let rF : ℕ → ℕ := schedFaultAt r C₀ σ
  have hft : σ.getD t 0 ∉ schedCache e C₀ σ t := by
    intro hft
    have hFt : σ.getD t 0 ∈ schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [← hagree t le_rfl]
      exact hft
    have hD : schedCache e C₀ σ (t + 1) = schedCache e C₀ σ t := by
      rw [schedCache]
      rw [if_pos hft]
    have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
        schedCache (fifoSchedule σ C₀) C₀ σ t := by
      rw [schedCache]
      rw [if_pos hFt]
    exact hdis ((hD.trans (hagree t le_rfl)).trans hF.symm)
  have hq'res : q' ∈ schedCache e C₀ σ t := by
    have hfd := first_disagree e σ C₀ hC₀ ht hagree hdis
    exact hfd.2.2
  have hsig_ne : σ.getD t 0 ≠ q' := by
    intro hsig
    exact hft (hsig ▸ hq'res)
  have hJ'len : t + 1 + j' < σ.length := by
    have hj'lt' : j' < (σ.drop (t + 1)).length := (nextUse_eq_some_iff.mp hj').1
    rw [List.length_drop] at hj'lt'
    omega
  constructor
  · -- misses: rF ≤ eF + 1 pointwise
    have hper : ∀ s, s < σ.length → rF s ≤ eF s + (if s = t + 1 + j' then 1 else 0) := by
      intro s hlen
      by_cases hst : s ≤ t
      · unfold rF eF r schedFaultAt
        rw [schedCache_repairSchedule_eq_e e t q' (t + 1 + j') (by omega) σ C₀ hst]
        rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
          simp [show s ≠ t + 1 + j' by omega]]
        omega
      · have hts' : t < s := by omega
        by_cases hsJ' : s < t + 1 + j'
        · -- in the window: faults coincide
          have hwin : schedCache r C₀ σ s = (schedCache e C₀ σ s).erase q' := by
            exact repairSchedule_window e σ C₀ hC₀ ht hagree hdis hnoop rfl hj' hts' (by omega)
          unfold rF eF r schedFaultAt
          rw [hwin]
          have hneq : σ.getD s 0 ≠ q' := getD_ne_nextUse (k := s) hj' (by omega) hsJ'
          by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
          · rw [if_pos hr]
            have hr' : σ.getD s 0 ∈ (schedCache e C₀ σ s).erase q' := by
              rw [Finset.mem_erase]
              constructor
              · exact hneq
              · exact hr
            rw [if_pos hr']
            rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
              simp [show s ≠ t + 1 + j' by omega]]
          · rw [if_neg hr]
            have hr' : σ.getD s 0 ∉ (schedCache e C₀ σ s).erase q' := by
              intro hm
              exact hr (Finset.mem_erase.mp hm).2
            rw [if_neg hr']
            rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
              simp [show s ≠ t + 1 + j' by omega]]
        · -- s ≥ J'
          by_cases hseq : s = t + 1 + j'
          · subst s
            -- at J': r faults
            unfold rF eF r schedFaultAt
            have hwin : schedCache r C₀ σ (t + 1 + j') =
                (schedCache e C₀ σ (t + 1 + j')).erase q' := by
              exact repairSchedule_window e σ C₀ hC₀ ht hagree hdis hnoop rfl hj'
                (by omega) (by rfl)
            rw [hwin]
            have hsig : σ.getD (t + 1 + j') 0 = q' := getD_eq_nextUse hj'
            have hq'notE : q' ∉ (schedCache e C₀ σ (t + 1 + j')).erase q' := by
              intro hm
              exact (Finset.mem_erase.mp hm).1 rfl
            rw [hsig]
            rw [if_neg hq'notE]
            have hind : (if t + 1 + j' = t + 1 + j' then 1 else 0) = 1 := by simp
            rw [hind]
            by_cases hr : q' ∈ schedCache e C₀ σ (t + 1 + j')
            · rw [if_pos hr]
            · rw [if_neg hr]
              omega
          · -- s > J': E ⊆ Ê
            have hsJ''' : t + 1 + j' < s := by omega
            have hsup : schedCache e C₀ σ s ⊆ schedCache r C₀ σ s := by
              exact repairSchedule_superset e σ C₀ hC₀ ht hagree hdis hnoop rfl hj' hsJ'''
            unfold rF eF r schedFaultAt
            by_cases hr : σ.getD s 0 ∈ schedCache e C₀ σ s
            · rw [if_pos hr]
              rw [if_pos (hsup hr)]
              rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                simp [show s ≠ t + 1 + j' by omega]]
            · rw [if_neg hr]
              by_cases hr' : σ.getD s 0 ∈ schedCache r C₀ σ s
              · rw [if_pos hr']
                rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                  simp [show s ≠ t + 1 + j' by omega]]
                omega
              · rw [if_neg hr']
                rw [show (if s = t + 1 + j' then 1 else 0) = 0 by
                  simp [show s ≠ t + 1 + j' by omega]]
    unfold schedMisses
    change (∑ s ∈ Finset.range σ.length, rF s) ≤ (∑ s ∈ Finset.range σ.length, eF s) + 1
    have hsum1 : (∑ s ∈ Finset.range σ.length, rF s) ≤
        ∑ s ∈ Finset.range σ.length, (eF s + (if s = t + 1 + j' then 1 else 0)) := by
      exact Finset.sum_le_sum (fun s hs => hper s (Finset.mem_range.mp hs))
    have hsum2 : (∑ s ∈ Finset.range σ.length, (eF s + (if s = t + 1 + j' then 1 else 0))) =
        (∑ s ∈ Finset.range σ.length, eF s) +
          ∑ s ∈ Finset.range σ.length, (if s = t + 1 + j' then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    have hsum3 : (∑ s ∈ Finset.range σ.length, (if s = t + 1 + j' then 1 else 0)) ≤ 1 := by
      rw [Finset.sum_ite_eq']
      by_cases hJ'in : t + 1 + j' ∈ Finset.range σ.length
      · simp [hJ'in]
      · simp [hJ'in]
    rw [hsum2] at hsum1
    exact le_trans hsum1 (Nat.add_le_add_left hsum3 _)
  · -- agree through t + 1
    intro s hs
    by_cases hs' : s ≤ t
    · rw [schedCache_repairSchedule_eq_e e t q' (t + 1 + j') (by omega) σ C₀ hs']
      exact hagree s hs'
    · have hst : s = t + 1 := by omega
      subst s
      have hbase : schedCache r C₀ σ (t + 1) = (schedCache e C₀ σ (t + 1)).erase q' := by
        exact repairSchedule_base e σ C₀ hC₀ ht hagree hdis hnoop rfl hj'
      have hF : schedCache (fifoSchedule σ C₀) C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
        rw [schedCache_fifoSchedule σ C₀ (t + 1)]
        unfold cacheSeq Policy.step
        rw [← schedCache_fifoSchedule σ C₀ t]
        rw [if_neg (by rw [← hagree t le_rfl]; exact hft)]
        congr 2
        · rw [hagree t le_rfl]
        · change farthestInFuture (schedCache (fifoSchedule σ C₀) C₀ σ t) σ t = q'
          rw [← hagree t le_rfl]
          rw [← fifo_evict_eq_farthest e σ C₀ hagree]
      have hE : schedCache r C₀ σ (t + 1) =
          insert (σ.getD t 0) ((schedCache e C₀ σ t).erase q') := by
        rw [hbase]
        rw [schedCache]
        rw [if_neg hft]
        rw [Finset.erase_eq_of_notMem hnoop]
        rw [Finset.erase_insert_of_ne hsig_ne]
      rw [hE, hF]

end Caching

end CLRS
