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

Current gaps:

- The optimality theorem (`fifo_optimal`: no eviction policy — even offline —
  has fewer misses than the farthest-in-future policy, CLRS Theorem 15.5)
  remains to be formalized: the classical exchange argument transforms an
  optimal policy at a fault into one that evicts the farthest-in-future page
  by simulating the two caches between the fault and the evicted page's next
  request.  The exchange schedule and its containment invariant are in place;
  the miss-counting comparison between the exchange schedule and `d` (using
  the invariant to charge bad events to requests of `q` or `q'`) is still
  deferred.
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
`d` keeps while the exchange schedule lacks it (evicting `q` when `d`
evicts `q'` and `q'` is absent, and a multi-set element — a page `d` does
not have — when `d` hits a request of `q` or `q'` that the exchange
schedule misses), so that no bad event (a fault where `d` hits) is
created.

The eviction decision at position `s`, based on the exchange schedule's
cache `C'` (the cache just before the request at `s`) and `d`'s cache. -/
noncomputable def exchangeDecision (d : ℕ → Page) (t : ℕ) (q q' : Page)
    (σ : List Page) (C₀ C' : Finset Page) (s : ℕ) : Page :=
  if s < t then d s
  else if s = t then q'
  else if d s = q' then (if q' ∈ C' then q' else q)
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
    (hdreduced : ∀ s, σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
    (s : ℕ) : (schedCache d C₀ σ (s + 1)).card = (schedCache d C₀ σ s).card := by
  rw [schedCache]
  by_cases hr : σ.getD s 0 ∈ schedCache d C₀ σ s
  · rw [if_pos hr]
  · rw [if_neg hr]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_erase_of_mem (hdreduced s hr)]
      have hc : 0 < (schedCache d C₀ σ s).card :=
        Finset.card_pos.mpr ⟨d s, hdreduced s hr⟩
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
    (hdreduced : ∀ s, σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
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
          rw [schedCache_card_const d C₀ σ hdreduced (t + n)]
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
    by_cases hq : q' ∈ C'
    · rw [if_pos hq]
      exact Or.inr (Or.inl rfl)
    · rw [if_neg hq]
      exact Or.inl rfl
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
    (hdreduced : ∀ s, σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s)
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
    by_cases hq : q' ∈ C'
    · rw [if_pos hq]
      exact Or.inr (Or.inl rfl)
    · rw [if_neg hq]
      exact Or.inl rfl
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
            exact hdreduced s hr
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
    (hdreduced : ∀ s, σ.getD s 0 ∉ schedCache d C₀ σ s → d s ∈ schedCache d C₀ σ s) :
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
              exact exchangeScheduleCore_card d t q q' σ C₀ hdreduced (by omega)
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
                exact exchangeScheduleCore_card d t q q' σ C₀ hdreduced (by omega)
              have hdec := exchangeDecision_of_fault d t q q' σ C₀
                (schedCache (exchangeSchedule d t q q' σ C₀) C₀ σ s) hdreduced hst hr hcard
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


end Caching

end CLRS
